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

module Iterator (D: Domains__.Domain.DOMAIN) = struct
  module Worklist = NodeSet
  
  let d_eq e1 e2 = D.leq e1 e2 && D.leq e2 e1

  let nodes_out node =
    List.map (fun arc -> arc.arc_dst) node.node_out

  let init_wl entry_point =
    nodes_out entry_point |> Worklist.of_list

  let widening_points cfg =
    let ar = Array.make 0 (List.length cfg.cfg_nodes) in

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
       let entry_env = List.fold_left D.join D.bottom (List.map (compute_arc map widen_points) node.node_in) in

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
      | CFG_assign_bool _ -> assert false (* TODO *) 
      | CFG_guard b -> D.guard env b
      | CFG_assert(b,_) ->
         if D.guard env b = D.bottom
         then D.bottom
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