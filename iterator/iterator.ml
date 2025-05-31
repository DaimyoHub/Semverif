(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)


 (*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph

type exn += Analysis_AssertionFailed of AbstractSyntax.extent * string

module Iterator (D: Domains.Domain.DOMAIN) = struct
  module Worklist = NodeSet
  
  let d_eq e1 e2 = D.leq e1 e2 && D.leq e2 e1

  let nodes_out node =
    List.map (fun arc -> arc.arc_dst) node.node_out

  let init_wl entry_point =
    nodes_out entry_point |> Worklist.of_list

  let widening_points cfg =
    let ar = Array.make (List.length cfg.cfg_nodes + 1) 0 in

    let rec go s n  =
      ar.(n.node_id) <- 1;

      let res = List.fold_left (
          fun acc node ->
          let v = ar.(node.node_id) in 
          if v = 0 then
            go acc node
          else if v = 1 then
            NodeSet.add node acc
          else acc
        ) s (nodes_out n)
      in
      ar.(n.node_id) <- 2;
      res
    in
    List.fold_left go (go NodeSet.empty cfg.cfg_init_entry ) (List.map (fun f -> f.func_entry) cfg.cfg_funcs)
      
  let rec compute wl map widen_points =
    match NodeSet.choose_opt wl with
    | None -> map
    | Some node ->
       let old_entry_env = NodeMap.find node map in 
       let entry_env = List.fold_right D.join (List.map (compute_arc map widen_points) node.node_in) D.bottom in

       let wl = NodeSet.remove node wl in
       
       if d_eq old_entry_env entry_env
       then compute wl map widen_points
       else
         let map = NodeMap.add node (if NodeSet.mem node widen_points then D.widen old_entry_env entry_env else entry_env) map in
         let wl =
           node 
           |> nodes_out
           |> Worklist.of_list
           |> Worklist.union wl
         in
         compute wl map widen_points
  and compute_arc map wp arc =
    let env = NodeMap.find arc.arc_src map in
    match arc.arc_inst with
      | CFG_skip _ -> env
      | CFG_assign(var,e) -> D.assign env var e
      | CFG_assign_bool _ -> assert false
      | CFG_guard b -> D.guard env b
      | CFG_assert(b, ext) ->
         if D.guard env b = D.bottom
         then
          begin
           let buf = Buffer.create 200 in
           let fmt = Format.formatter_of_buffer buf in
           D.pp fmt env;
           Format.pp_print_flush fmt ();
           raise (Analysis_AssertionFailed (ext, Buffer.contents buf))
          end
         else env 
      | CFG_call f ->
         let map = compute (init_wl f.func_entry) (NodeMap.add f.func_entry env map) wp in
         NodeMap.find f.func_exit map 
    
  let iterate cfg = 
    let envs = List.fold_left (fun acc node -> NodeMap.add node D.init acc) NodeMap.empty cfg.cfg_nodes in
    let wl = init_wl cfg.cfg_init_entry in
    let wp = widening_points cfg in
    
    compute wl envs wp   
end

module Iterator_part (V : Domains.Domain.VARS) = struct
  module Worklist = NodeSet
  module D = Domains.Roots.Make_part_product (V)
  
  let d_eq e1 e2 = D.leq e1 e2 && D.leq e2 e1

  let nodes_out node =
    List.map (fun arc -> arc.arc_dst) node.node_out

  let init_wl entry_point =
    nodes_out entry_point |> Worklist.of_list

  let widening_points cfg =
    let ar = Array.make (List.length cfg.cfg_nodes + 1) 0 in

    let rec go s n  =
      ar.(n.node_id) <- 1;

      let res = List.fold_left (
          fun acc node ->
          let v = ar.(node.node_id) in 
          if v = 0 then
            go acc node
          else if v = 1 then
            NodeSet.add node acc
          else acc
        ) s (nodes_out n)
      in
      ar.(n.node_id) <- 2;
      res
    in
    List.fold_left go (go NodeSet.empty cfg.cfg_init_entry ) (List.map (fun f -> f.func_entry) cfg.cfg_funcs)
      
  let rec compute wl map widen_points =
    match NodeSet.choose_opt wl with
    | None -> (print_endline "1"; map)
    | Some node ->
       print_endline "2";
       let old_entry_env = NodeMap.find node map in 
       let entry_env = List.fold_right D.join (List.map (compute_arc map widen_points) node.node_in) D.bottom in

       let wl = NodeSet.remove node wl in
       
       if d_eq old_entry_env entry_env
       then compute wl map widen_points
       else
         let map = NodeMap.add node (if NodeSet.mem node widen_points then D.widen old_entry_env entry_env else entry_env) map in
         let wl =
           node 
           |> nodes_out
           |> Worklist.of_list
           |> Worklist.union wl
         in
         compute wl map widen_points
  and compute_arc map wp arc =
    let env = NodeMap.find arc.arc_src map in
    match arc.arc_inst with
      | CFG_skip _ -> env
      | CFG_assign(var, e) -> D.assign env var e
      | CFG_assign_bool (var, b) -> (D.split env var.var_name b; env)
      | CFG_guard b -> begin
          match b with
          | CFG_bool_unary (AbstractSyntax.AST_NOT, CFG_bool_var var) ->
              (D.rm_bool_cond env var.var_name; env)
          | CFG_bool_var var ->
              (D.add_bool_cond env var.var_name; env)
          | _ -> D.guard env b
        end
      | CFG_assert(b, ext) ->
         if D.guard env b = D.bottom
         then
          begin
           let buf = Buffer.create 200 in
           let fmt = Format.formatter_of_buffer buf in
           D.pp fmt env;
           Format.pp_print_flush fmt ();
           raise (Analysis_AssertionFailed (ext, Buffer.contents buf))
          end
         else env 
      | CFG_call f ->
         let map = compute (init_wl f.func_entry) (NodeMap.add f.func_entry env map) wp in
         NodeMap.find f.func_exit map 
    
  let iterate cfg = 
    let envs = List.fold_left (fun acc node -> NodeMap.add node (if node <> cfg.cfg_init_entry then D.bottom else D.init) acc) NodeMap.empty cfg.cfg_nodes in
    let wl = init_wl cfg.cfg_init_entry in
    let wp = widening_points cfg in
    
    compute wl envs wp   
end

let iterate_part cfg =
  let module I = Iterator_part (struct let support = cfg.cfg_vars end) in 
  let _ = I.iterate cfg in ()

let iterate (module Dom : Domains.Domain.DOMAIN) cfg = 
  let module I = Iterator(Dom) in 
  let _ = I.iterate cfg in ()


