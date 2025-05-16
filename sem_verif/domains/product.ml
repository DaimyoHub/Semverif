open Io
open Domain
open States

module NR_interval = Non_relational (Interval)

type t = prod

let init = Prd { intvl = Itop; sign = Stop }

let top = Prd { intvl = Itop; sign = Stop }

let bottom = Pbot

let const z = Prd { intvl = Interval.const z; sign = Sign.const z }

let rand a b = Prd { intvl = Interval.rand a b; sign = Sign.rand a b }

let refine p =
  let intvl_of_sign = function
    | Sbot -> Ibot
    | Stop -> Itop
    | Neg -> Intvl (Ninf, Interval.Util.neg (Z Z.one))
    | Pos -> Intvl (Z Z.one, Pinf)
    | Nul -> Intvl (Z Z.zero, Z Z.zero)
  in
  let sign_of_intvl = function
    | Ibot -> Sbot
    | Itop -> Stop
    | intvl -> 
        if Interval.leq intvl (intvl_of_sign Neg) then Neg
        else if Interval.leq intvl (intvl_of_sign Pos) then Pos
        else if Interval.leq intvl (intvl_of_sign Nul) then Nul
        else Stop
  in
  match p with
  | Prd { intvl; sign } ->
      if Sign.leq sign (sign_of_intvl intvl) then
        Prd { intvl = Interval.meet (intvl_of_sign sign) intvl; sign }
      else p
  | _ -> Pbot

let unary p op =
  let p' =
    match p with
    | Prd p -> Prd { intvl = Interval.unary p.intvl op; sign = Sign.unary p.sign op }
    | Pbot -> Pbot
  in refine p' (* seems useless to refine here but why not *)

let binary lhs rhs op =
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs -> Prd {
        intvl = Interval.binary lhs.intvl rhs.intvl op;
        sign = Sign.binary lhs.sign rhs.sign op
      }
    | _ -> Pbot (* should bottom strictness hold for the product domain ? (i think so) *)
  in refine p

let compare lhs rhs op =
  let ic = Interval.compare and sc = Sign.compare in
  match
    (match lhs, rhs with
    | Prd lhs, Prd rhs -> Some (ic lhs.intvl rhs.intvl op, sc rhs.sign rhs.sign op)
    | Pbot, Prd p -> Some (ic Ibot p.intvl op, sc Sbot p.sign op)
    | Prd p, Pbot -> Some (ic p.intvl Ibot op, sc p.sign Sbot op)
    | Pbot, Pbot -> None)
  with
  | Some ((a, b), (c, d)) -> Prd { intvl = a; sign = c }, Prd { intvl = b; sign = d }
  | None -> Pbot, Pbot

let join lhs rhs =
  let ij = Interval.join and sj = Sign.join in
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs ->
        Prd { intvl = ij lhs.intvl rhs.intvl; sign = sj lhs.sign rhs.sign }
    | Pbot, Prd p | Prd p, Pbot ->
        Prd { intvl = ij Ibot p.intvl; sign = sj Sbot p.sign }
    | Pbot, Pbot -> Pbot
  in refine p

let meet lhs rhs =
  let im = Interval.meet and sm = Sign.meet in
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs ->
        Prd { intvl = im lhs.intvl rhs.intvl; sign = sm lhs.sign rhs.sign }
    | Pbot, Prd p | Prd p, Pbot ->
        Prd { intvl = im Ibot p.intvl; sign = sm Sbot p.sign }
    | Pbot, Pbot -> Pbot
  in refine p

(* I directly implemented the formula given in class : x_n+1 = widen x_n (rho (F# x_n)).
   I refine the right operand, assuming that it corresponds to F#(x_n) and I do not
   refine after widening *)
let widen lhs rhs =
  let _rhs' = refine rhs in
  (* apply widening on lhs and rhs' *)
  failwith "todo"

let narrow lhs rhs = failwith "todo"

let leq lhs rhs =
  match lhs, rhs with
  | Pbot, _ -> true
  | Prd _, Pbot -> false
  | Prd lhs, Prd rhs -> Interval.leq lhs.intvl rhs.intvl && Sign.leq lhs.sign rhs.sign

let is_bottom = (=) Pbot

let pp _ _ = failwith "todo"
