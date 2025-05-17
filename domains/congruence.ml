open States
open Frontend.AbstractSyntax

module Util =
 struct
  let gcd a b =
    let rec aux a b =
      if b = 0 then a
      else aux b (a mod b)
    in aux (abs a) (abs b)

  let lcm a b =
    if a = 0 || b = 0 then 0
    else abs (a * b) / gcd a b

  let extended_gcd a b =
    let rec inner r1 r2 s1 s2 t1 t2 =
      if r2 = 0 then (r1, s1, t1)
      else
        let q = r1 / r2 and r = r1 mod r2 in inner r2 r s2 (s1 - q * s2) t2 (t1 - q * t2)
    in inner a b 1 0 0 1
 end
type t = congr

let top = Ctop

let to_top = function
  | Cgr (1, 0) -> Ctop
  | c -> c

let bottom = Cbot

let const z = Cgr (0, Z.to_int z)

let rand a b = to_top (if a = b then Cgr (0, Z.to_int a) else Cgr (1, 0))

let unary c op =
  let c = to_top c in
  match c, op with
  | _, AST_UNARY_PLUS -> c
  | Cgr (a, b), _ -> to_top (Cgr (a, -b))
  | Ctop, _ -> Ctop
  | _ -> Cbot

let rec binary lhs rhs op =
  let lhs, rhs = to_top lhs, to_top rhs in
  let inner lhs rhs =
    match lhs, rhs with
    | Ctop, _ | _, Ctop -> Ctop
    | Cbot, _ | _, Cbot -> Cbot
    | Cgr (a, b), Cgr (a', b') -> begin
        match op with
        | AST_PLUS -> Cgr (Util.gcd a a', b + b')
        | AST_MINUS -> binary lhs (unary rhs AST_UNARY_MINUS) AST_PLUS
        | AST_MULTIPLY ->
            let gcd a b c = Util.(gcd (gcd a b) c) in
            Cgr (gcd (a * a') (a * b') (a' * b), b * b')
        | AST_DIVIDE ->
            if a' = 0 && b' = 0 then Cbot
            else if a' = 0 && b' <> 0 && b' mod a = 0 && b' mod b = 0 then 
              Cgr (a / (abs b'), b / b')
            else Ctop
        | AST_MODULO -> failwith "todo"
      end
  in to_top (inner lhs rhs)

let leq lhs rhs =
  match lhs, rhs with
  | _, Ctop | Cbot, _ -> true
  | _, Cbot | Ctop, _ -> false
  | Cgr (a, b), Cgr (a', b') -> a' mod a = 0 && b mod a' = b'

let compare lhs rhs op =
  match op with
  | AST_EQUAL -> begin
      match lhs, rhs with
      | Ctop, _ -> rhs, rhs
      | _, Ctop -> lhs, lhs
      | Cbot, _ | _, Cbot -> Cbot, Cbot
      | Cgr (a, b), Cgr (a', b') ->
          if leq lhs rhs then lhs, lhs else if leq rhs lhs then rhs, rhs else Cbot, Cbot
    end
  | AST_NOT_EQUAL ->
      if not (leq lhs rhs) && not (leq rhs lhs) then lhs, rhs else Ctop, Ctop
  | _ -> lhs, rhs

let join lhs rhs =
  let lhs, rhs = to_top lhs, to_top rhs in
  let inner lhs rhs =
    match lhs, rhs with
    | Ctop, _ | _, Ctop -> Ctop
    | Cbot, _ -> rhs
    | _, Cbot -> lhs
    | Cgr (a, b), Cgr (a', b') ->
        let gcd a b c = Util.(gcd (gcd a b) c) in
        Cgr (gcd a a' (abs (b - b')), b)
  in to_top (inner lhs rhs)

let meet lhs rhs =
  let lhs, rhs = to_top lhs, to_top rhs in
  let inner lhs rhs =
    match lhs, rhs with
    | Cbot, _ | _, Cbot -> Cbot
    | Ctop, _ -> rhs
    | _, Ctop -> lhs
    | Cgr (a, b), Cgr (a', b') ->
        if b mod (Util.gcd a a') = b' then (*flemme*) failwith "todo" else Cbot
  in to_top (inner lhs rhs)

let widen = join

let narrow lhs rhs =
  let lhs, rhs = to_top lhs, to_top rhs in
  match lhs, rhs with
  | Ctop, _ -> rhs
  | _ -> lhs

let widen lhs rhs = Ctop

let is_bottom = (=) Cbot

let pp _ _ = failwith ""
