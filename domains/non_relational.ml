open Domain
open Value_domain
open Frontend.ControlFlowGraph
open Frontend.AbstractSyntax

module Env = VarMap

module Make (D : Value_domain.VALUE_DOMAIN) (V : VARS) = 
 struct 
  type t = D.t Env.t

  let init = Env.empty

  let bottom = Env.empty

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

  let join lhs rhs =
    Env.merge
      (fun var s_opt s_opt' ->
        match s_opt, s_opt' with
        | Some a, Some b -> Some (D.join a b)
        | Some a, _ | _, Some a -> Some a
        | _ -> None)
      lhs rhs

  let meet lhs rhs =
    Env.merge
      (fun _ s_opt s_opt' ->
        match s_opt, s_opt' with
        | None, _ | _, None -> None
        | Some a, Some b -> Some (D.meet a b))
      lhs rhs

  let rec guard env = function
    | CFG_bool_const b -> if b then env else bottom
    | CFG_bool_rand -> env
    | CFG_compare (bop, lhs, rhs) ->
        let a, b = D.compare (eval env lhs) (eval env rhs) bop in
        (*c'est de la merde*)Env.filter (fun _ s -> D.leq s a || D.leq s b) env
    | CFG_bool_unary (AST_NOT, expr) -> compl env expr
    | CFG_bool_binary (AST_AND, lhs, rhs) -> meet (guard env lhs) (guard env rhs)
    | CFG_bool_binary (AST_OR, lhs, rhs) -> join (guard env lhs) (guard env rhs)

  and compl env = function
    | CFG_bool_const b -> if b then bottom else env
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
        let a, b = D.compare (eval env lhs) (eval env rhs) bop in
        Env.filter (fun _ s -> D.leq s a || D.leq s b) env
    | CFG_bool_unary (AST_NOT, expr) -> guard env expr
    | CFG_bool_binary (AST_OR, lhs, rhs) -> join (guard env lhs) (guard env rhs)
    | CFG_bool_binary (AST_AND, lhs, rhs) -> meet (guard env lhs) (guard env rhs)

  let widen _ _ = Env.empty

  let narrow _ _ = Env.empty

  let leq lhs rhs =
    Env.for_all
      (fun var state ->
        match Env.find_opt var rhs with
        | Some state' -> D.leq state state'
        | None -> false)
      lhs

  let is_bottom = Env.is_empty

  let pp fmt env =
    Env.iter
      (fun var state -> Format.fprintf fmt "%s: " var.var_name; D.pp fmt state)
      env
 end

