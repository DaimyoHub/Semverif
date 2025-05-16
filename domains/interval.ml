open Frontend.AbstractSyntax
open Io
open States

(* This module contains some utilitaries to manipulate extended signed integers *)
module Util =
 struct
  open Z

  let min lhs rhs =
    match lhs, rhs with
    | Ninf, _ | _, Ninf -> Ninf
    | Pinf, _ -> rhs
    | _, Pinf -> lhs
    | Z a, Z b -> if a < b then lhs else rhs

  let max lhs rhs =
    match lhs, rhs with
    | Pinf, _ | _, Pinf -> Pinf
    | Ninf, _ -> rhs
    | _, Ninf -> lhs
    | Z a, Z b -> if a > b then lhs else rhs

  let ( + ) lhs rhs =
    match lhs, rhs with
    | Pinf, Ninf | Ninf, Pinf -> failwith "undefined"
    | Pinf, _ | _, Pinf -> Pinf
    | Ninf, _ | _, Ninf -> Ninf
    | Z a, Z b -> Z (a + b)

  let ( - ) lhs rhs =
    match lhs, rhs with
    | Pinf, Ninf | Ninf, Pinf -> failwith "undefined"
    | Ninf, _ -> Ninf
    | _, Ninf | Pinf, _ -> Pinf
    | _, Pinf -> Ninf
    | Z a, Z b -> Z (a - b)

  let ( * ) lhs rhs =
    match lhs, rhs with
    | Z a, Pinf | Pinf, Z a | Z a, Ninf | Ninf, Z a when a = Z.zero -> Z Z.zero
    | Z a, Pinf | Pinf, Z a -> if a > Z.zero then Pinf else Ninf
    | Z a, Ninf | Ninf, Z a -> if a > Z.zero then Ninf else Pinf
    | Pinf, Pinf | Ninf, Ninf -> Pinf
    | Pinf, Ninf | Ninf, Pinf -> Ninf
    | Z a, Z b -> Z (a * b)

  let ( / ) lhs rhs =
    match lhs, rhs with
    | Z _, Pinf | Z _, Ninf | Pinf, Pinf | Ninf, Ninf | Pinf, Ninf | Ninf, Pinf ->
        Z Z.zero
    | Pinf, Z a -> if a > Z.zero then Pinf else Ninf
    | Ninf, Z a -> if a > Z.zero then Ninf else Pinf
    | Z a, Z b -> Z (a / b)

  let ( > ) lhs rhs =
    match lhs, rhs with
    | Ninf, Pinf -> true
    | Ninf, Ninf | Pinf, Pinf -> false
    | Z a, Z b -> a > b
    | _ -> false

  let ( = ) lhs rhs =
    match lhs, rhs with
    | Ninf, Ninf | Pinf, Pinf -> true
    | Z a, Z b -> a = b
    | _ -> false

  let ( <= ) lhs rhs = (lhs = rhs) || (lhs < rhs)

  let neg = function Ninf -> Pinf | Pinf -> Ninf | Z a -> Z (-a)
 end

type t = intvl

let top = Itop

(* The top element of this domain corresponds to the interval [-inf, +inf] but we should
   represent it thanks to the constructor Itop for uniformity *)
let to_top = function Intvl (Ninf, Pinf) -> Itop | a -> a

let bottom = Ibot

let is_bottom = (=) Ibot

let const z = Intvl (Z z, Z z)

let rand a b = if a <= b then Intvl (Z a, Z b) else Ibot

let unary intvl op =
  let intvl = to_top intvl in
  let open Util in
  match intvl, op with
  | Ibot, _ -> Ibot
  | Itop, _ -> Itop
  | _, AST_UNARY_PLUS -> intvl
  | Intvl (a, b), AST_UNARY_MINUS -> to_top (Intvl (neg b, neg a))

let bwd_unary _ _ _ = failwith "TODO"

let bwd_binary _ _ _ _ = failwith "TODO"

let join lhs rhs =
  let lhs = to_top lhs and rhs = to_top rhs in
  match lhs, rhs with
  | Itop, _ | _, Itop -> Itop
  | Ibot, _ -> rhs
  | _, Ibot -> lhs
  | Intvl (a, b), Intvl (c, d) ->
      let m = min a c and m' = max b d in to_top (Intvl (m, m'))

let meet lhs rhs =
  let lhs = to_top lhs and rhs = to_top rhs in
  match lhs, rhs with
  | Ibot, _ | _, Ibot -> Ibot
  | Itop, _ -> rhs
  | _, Itop -> lhs
  | Intvl (a, b), Intvl (c, d) ->
      let m = max a c and m' = min b d in
      if m <= m' then to_top (Intvl (m, m')) else Ibot

(* This implementation follows the rules given in
     https://www.di.ens.fr/~rival/semverif-2015/sem-11-ai.pdf *)
let binary lhs rhs op =
  let open Util in
  let rec inner lhs rhs op =
    let lhs = to_top lhs and rhs = to_top rhs in
    match lhs, rhs with
    | Ibot, _ | _, Ibot -> Ibot
    | Itop, _ | _, Itop -> Itop
    | Intvl (a, b), Intvl (c, d) -> begin
        match op with
        | AST_PLUS -> Intvl (a + c, b + d)
        | AST_MINUS -> Intvl (a - d, b - c)
        | AST_MULTIPLY ->
            let l_bound = min (min (a * c) (a * d)) (min (b * c) (b * d))
            and r_bound = max (max (a * c) (a * d)) (max (b * c) (b * d))
            in Intvl (l_bound, r_bound)
        | AST_DIVIDE -> 
            if Z Z.one <= c then
              Intvl (min (a / c) (a / d), max (b / c) (b / d))
            else if d <= neg (Z Z.one) then
              Intvl (min (c / c) (b / d), max (a / c) (a / d))
            else
              let div lhs rhs = inner lhs rhs AST_DIVIDE in
              join
                (div lhs (meet rhs (Intvl (Z Z.one, Pinf))))
                (div lhs (meet rhs (Intvl (Ninf, neg (Z Z.one)))))
        | AST_MODULO -> failwith "todo"
      end
  in to_top (inner lhs rhs op)

let rec compare lhs rhs op = 
  let open Util in
  let inner lhs rhs op =
    let lhs = to_top lhs and rhs = to_top rhs in
    match op with
	  | AST_EQUAL -> meet lhs rhs, meet lhs rhs
	  | AST_NOT_EQUAL -> begin
			  match lhs, rhs with
        (* [-inf [c...d] +inf] -> [-inf, +inf], [] *)
        | Itop, _ -> Itop, Ibot 
        | _, Itop -> Ibot, Itop
        (* The empty interval is never equal to any other interval *)
			  | Ibot, _ | _, Ibot -> lhs, rhs
			  | Intvl (a, b), Intvl (c, d) ->
            (* [c   d] [a   b] -> [], [] *)
            if d <= a then lhs, rhs
            else if c <= b then
              (* [c   [a...b]   d] -> [], [c, d] *)
              if c <= a then Ibot, rhs
              (* [a...[c...b]   d] -> [a, c], [b, d] *)
              else Intvl (a, c), Intvl (b, d)
            (* [a   b] [c   d] -> [a, b], [c   d] *)
            else lhs, rhs
		  end
	  | AST_LESS ->
        let a, b = compare lhs rhs AST_LESS_EQUAL
        and c, d = compare lhs rhs AST_NOT_EQUAL
        in meet a c, meet b d
	  | AST_LESS_EQUAL -> begin
			  match lhs, rhs with
			  | Itop, Itop | Ibot, _ | _, Ibot -> lhs, rhs
			  | Intvl (a, b), Itop -> Intvl (a, b), Intvl (a, Pinf)
			  | Itop, Intvl (a, b) -> Intvl (Ninf, b), Intvl (a, b)
			  | Intvl (a, b), Intvl (c, d) ->
            if d <= a then Ibot, Ibot
            else if c <= b then
              (* [c   [a...b]   d] -> [], [c, d] *)
              if c <= a then Intvl (c, b), Intvl (a, d)
              (* [a...[c...b]   d] -> [a, c], [b, d] *)
              else lhs, rhs
            (* [a   b] [c   d] -> [a, b], [c   d] *)
            else lhs, rhs
		  end
	  | AST_GREATER -> let a, b = compare rhs lhs AST_LESS in b, a
	  | AST_GREATER_EQUAL -> let a, b = compare rhs lhs AST_LESS_EQUAL in b, a
  in let ra, rb = inner lhs rhs op in to_top ra, to_top rb

let narrow lhs rhs = failwith "todo"

let widen lhs rhs =
  match to_top lhs, to_top rhs with
  | Itop, rhs -> rhs
  | Ibot, _ | _, Itop | _, Ibot -> Itop
  | Intvl (a, b), Intvl (c, d) ->
      let l_bound =
        if a <= c then a else Ninf and r_bound = if b >= d then b else Pinf
      in to_top (Intvl (l_bound, r_bound))

let leq lhs rhs =
  let lhs = to_top lhs and rhs = to_top rhs in
  match lhs, rhs with
  | _, Itop | Ibot, _ -> true
  | Itop, _ | _, Ibot -> false
  | Intvl (a, b), Intvl (c, d) -> c <= a && b <= d

let pp fmt intvl =
  let intvl = to_top intvl in
  Format.fprintf fmt "%s"
    (match intvl with
      | Itop -> "[-inf, +inf]"
      | Ibot -> "empty"
      | Intvl (a, b) ->
          let fmt_z = function Pinf -> "+inf" | Ninf -> "-inf" | Z n -> Z.to_string n in
          "[" ^ fmt_z a ^ ", " ^ fmt_z b ^ "]")
