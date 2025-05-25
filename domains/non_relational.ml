open Domain
open Value_domain
open Frontend.ControlFlowGraph
open Frontend.AbstractSyntax

module Env = VarMap

module Make (D : VALUE_DOMAIN) (V : VARS) = 
 struct 
  type t = D.t Env.t

  let init = List.fold_left (fun acc var -> Env.add var (D.const Z.zero) acc) Env.empty V.support
  
  let bottom = Env.empty
  let is_bottom = Env.is_empty

  let get_constraint env var = Env.find var env

  let rec eval env = function
    | CFG_int_const z -> D.const z
    | CFG_int_binary (bop, lhs, rhs) -> D.binary (eval env lhs) (eval env rhs) bop
    | CFG_int_unary (uop, expr) -> D.unary (eval env expr) uop
    | CFG_int_rand (a, b) -> D.rand a b
    | CFG_int_var var -> begin
        match Env.find_opt var env with
        | Some state -> state
        | None -> D.bottom
      end

  let assign env var expr = Env.add var (eval env expr) env

  let map2 f lhs rhs =
    Env.merge
      (fun var s_opt s_opt' ->
        match s_opt, s_opt' with
        | Some a, Some b -> Some (f a b)
        | Some a, _ | _, Some a -> Some a
        | _ -> None)
      lhs rhs

  let parallel f x y = if is_bottom x then y else if is_bottom y then x else f x y 
  
  let join = map2 D.join |> parallel
  let widen = map2 D.widen |> parallel
  let narrow = map2 D.narrow |> parallel

  (* Si l'on obtient une contradiction localement, on la propage. Le meet n'est pas un opérateur parallèle) *)
  let meet lhs rhs =
    try
      map2
        (fun x y ->
          let z = D.meet x y in
          if D.is_bottom z then raise Not_found else z)
        lhs rhs
    with Not_found -> bottom 
       
  let rec ensures e v env = match e with
    | CFG_int_binary(op,e1,e2) ->
       let v1' = eval env e1 in
       let v2' = eval env e1 in
       let v1, v2 = D.bwd_binary v1' v2' op v in
       meet (ensures e1 v1 env) (ensures e2 v2 env)
    | CFG_int_unary(op, e) ->
       let v' = eval env e in
       ensures e (D.bwd_unary v' op v) env
    | CFG_int_const z -> if D.leq v (D.const z) then env else bottom
    | CFG_int_rand(lo, hi) -> if D.leq v (D.rand lo hi) then  env else bottom 
    | CFG_int_var var -> VarMap.add var v env

  let rec guard env = function
    | CFG_bool_var var -> if D.is_bottom (Env.find var env) then bottom else env
    | CFG_bool_const true -> env
    | CFG_bool_const false -> bottom
    | CFG_bool_rand -> env
    | CFG_compare (op, lhs, rhs) ->
       let v_lhs, v_rhs = D.compare (eval env lhs) (eval env rhs) op in
       meet (ensures lhs v_lhs env) (ensures rhs v_rhs env)
    | CFG_bool_unary (AST_NOT, expr) -> compl env expr
    | CFG_bool_binary (AST_AND, lhs, rhs) -> meet (guard env lhs) (guard env rhs)
    | CFG_bool_binary (AST_OR, lhs, rhs) -> join (guard env lhs) (guard env rhs)

  and compl env = function
    | CFG_bool_var var -> if D.is_bottom (Env.find var env) then env else bottom
    | CFG_bool_const true -> bottom
    | CFG_bool_const false -> env 
    | CFG_bool_rand -> env
    | CFG_compare (bop, lhs, rhs) ->
        let bop =
          match bop with
          | AST_EQUAL -> AST_NOT_EQUAL
          | AST_NOT_EQUAL -> AST_EQUAL
          | AST_GREATER -> AST_LESS
          | AST_LESS -> AST_GREATER_EQUAL
          | AST_GREATER_EQUAL -> AST_LESS
          | AST_LESS_EQUAL -> AST_GREATER
        in
        CFG_compare(bop, lhs, rhs) |> guard env 
    | CFG_bool_unary (AST_NOT, expr) -> guard env expr
    | CFG_bool_binary (AST_OR, lhs, rhs) -> join (guard env lhs) (guard env rhs)
    | CFG_bool_binary (AST_AND, lhs, rhs) -> meet (guard env lhs) (guard env rhs)


  let leq lhs rhs =
    Env.for_all
      (fun var state ->
        match Env.find_opt var rhs with
        | Some state' -> D.leq state state'
        | None -> false)
      lhs



  let pp fmt env =
    print_endline "{\n";
    Env.iter
      (fun var state ->
        Format.fprintf fmt "\t%s: " var.var_name;
        D.pp fmt state;
        print_endline "")
      env;
    print_endline "}"
 end

