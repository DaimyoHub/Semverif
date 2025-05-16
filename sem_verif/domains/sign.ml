open Frontend.AbstractSyntax
open States

type t = sign

(* unrestricted value: [-oo,+oo] *)
let top = Stop

(* bottom value: empty set *)
let bottom = Sbot

(* constant: {c} *)
let const z = 
  let cmp = Z.compare z Z.zero in
  if cmp < 0 then Neg else if cmp = 0 then Nul else Pos

(* interval: [a,b] *)
let rand _ _ = Stop

(* unary operation *)
let unary sign = function
  | AST_UNARY_PLUS -> sign
  | AST_UNARY_MINUS -> begin
      match sign with
      | Stop | Sbot | Nul -> sign
      | Pos -> Neg
      | Neg -> Pos
    end

(* binary operation *)
let rec binary lhs rhs = function
  | AST_PLUS -> begin
      match lhs, rhs with
      | Sbot, _ | _, Sbot -> Sbot
      | Stop, _ | _, Stop | Neg, Pos | Pos, Neg -> Stop
      | Neg, Neg | Neg, Nul -> Neg
      | Pos, Nul | Pos, Pos -> Pos
      | Nul, _ -> rhs
    end
  | AST_MULTIPLY -> begin
      match lhs, rhs with
      | Sbot, _ | _, Sbot -> Sbot
      | Neg, Neg -> Pos
      | Neg, Nul | Stop, Nul | Nul, _ -> Nul
      | Neg, Pos -> Neg
      | Neg, Stop | Stop, _ -> Stop
      | Pos, _ -> rhs
    end
  | AST_MINUS -> binary lhs (unary rhs AST_UNARY_MINUS) AST_PLUS
  | AST_DIVIDE -> begin
      match lhs, rhs with
      | _, Nul -> Sbot
      | Sbot, _ | _, Sbot -> Sbot
      | Nul, _ -> Nul
      | Stop, _ | _, Stop -> Stop
      | Pos, Neg | Neg, Pos -> Neg
      | Pos, Pos | Neg, Neg -> Pos
    end
  | AST_MODULO -> failwith "todo"

let join lhs rhs =
  match lhs, rhs with
  | Stop, _ | _, Stop -> Stop
  | Sbot, _ -> rhs
  | _, Sbot -> lhs
  | _ -> Stop

let meet lhs rhs =
  match lhs, rhs with
  | Sbot, _ | _, Sbot -> Sbot
  | Stop, _ -> rhs
  | _, Stop -> lhs
  | _ -> Sbot

let rec compare lhs rhs = function
  | AST_LESS -> begin
      match lhs, rhs with
      | Sbot, _ -> Sbot, rhs
      | _, Sbot -> lhs, Sbot
      | Pos, _ -> Sbot, Sbot
      | Stop, Neg | Stop, Stop | Nul, Neg | Nul, Nul | Neg, Neg -> Sbot, Sbot
      | Stop, Nul -> Neg, Sbot
      | Stop, Pos -> Stop, Sbot 
      | Neg, Stop -> Sbot, Stop
      | Neg, _ -> Neg, rhs
      | Nul, Pos -> Nul, Pos
      | Nul, Stop -> Sbot, Pos
    end
  | AST_LESS_EQUAL ->
      let a, b = compare lhs rhs AST_LESS and c, d = compare lhs rhs AST_EQUAL in
      join a c, join b d
  | AST_GREATER -> let a, b = compare rhs lhs AST_LESS in b, a
  | AST_GREATER_EQUAL ->
      let a, b = compare lhs rhs AST_GREATER and c, d = compare lhs rhs AST_EQUAL in
      join a c, join b d
  | AST_EQUAL -> begin
      match lhs, rhs with
      | Sbot, _ -> Sbot, rhs
      | _, Sbot -> lhs, Sbot
      | Stop, _ | _, Stop -> rhs, rhs
      | Neg, Neg | Nul, Nul | Pos, Pos -> lhs, rhs
      | _ -> Sbot, Sbot
    end
  | AST_NOT_EQUAL -> begin
      let a, b = compare lhs rhs AST_LESS and c, d = compare lhs rhs AST_GREATER in
      join a c, join b d
    end

let bwd_unary _ _ _ = failwith "todo"

let bwd_binary _ _ _ _ = failwith "todo"

let widen _ _ = failwith "todo"

let narrow _ _ = failwith "todo"

let leq lhs rhs =
  match lhs, rhs with
  | Sbot, _ -> true
  | _, Stop -> true
  | _ -> false

let is_bottom = (=) Sbot

let pp fmt sign =
  Format.fprintf fmt "%s"
    (match sign with
      | Sbot -> "{}"
      | Stop -> "{pos, neg, nul}"
      | Neg -> "{neg}"
      | Nul -> "{nul}"
      | Pos -> "{pos}")

