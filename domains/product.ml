(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* Reduced product's implementation *)

open Domain
open States

type t = prod

let init = Prd { intvl = Ibot; sign = Sbot; congr = Cbot }

let top = Prd { intvl = Itop; sign = Stop; congr = Ctop }

let bottom = Pbot

let const z =
  Prd { intvl = Interval.const z; sign = Sign.const z; congr = Congruence.const z }

let rand a b =
  Prd { intvl = Interval.rand a b; sign = Sign.rand a b; congr = Congruence.rand a b }

(* The sign domain and the congruence domain both compute properties that can be used to
   refine the computations of the interval domain. *)
let refine p =
  (* The congruence domain could thin an interval, troncating slices from it, formed by
     its bounds. More preciselly, given an interval [A; B] the lower bound may be 
     refined to the least element of the ring greater than A, dually, the upper bound B
     may be refined to the greatest element of the ring less than B *)
  let rec refine_intvl_with_congr intvl congr =
    (* [nearest_mult n a b limit ~sup: b] computes the nearest number of the ring aZ+b
       which is either greater than n (if sup is true) or less than n (if sup is false).
       The limit is the number not to exceed. For instance, [nearest 2 4 0 3 ~sup: true]
       gives the number 3, as the nearest multiple of 4 greater than 2 is greater than
       the limit 3. *)
    let rec nearest_mult n a b limit ~sup =
      let cop, bop = if sup then (>=), (+) else (<=), (-) in
      match limit with
      | Some l -> 
          if cop n l then l
          else if n mod a <> b then nearest_mult (bop n 1) a b limit sup
          else n
      | None -> nearest_mult (bop n 1) a b limit sup
    in
    match congr with
    | Cgr (a, b) -> begin
        let sup_mult n l = Z (Z.of_int (nearest_mult (Z.to_int n) a b l ~sup: true))
        and inf_mult m l = Z (Z.of_int (nearest_mult (Z.to_int m) a b l ~sup: false))
        in
        match intvl with
        | Intvl (Z n, Z m) ->
            Intvl (sup_mult n (Some (Z.to_int m)), inf_mult m (Some (Z.to_int n)))
        | Intvl (Z n, Pinf) -> Intvl (sup_mult n None, Pinf)
        | Intvl (Ninf, Z n) -> Intvl (Ninf, inf_mult n None)
        | _ -> intvl
      end
    | Ctop ->
        let refined_intvl = refine_intvl_with_congr intvl (Cgr (1, 0)) in
        if Interval.leq refined_intvl intvl && intvl <> Ibot then refined_intvl
        else intvl
    | Cbot -> intvl
  in
  (* The sign domain could troncate an interval according to a computed sign. *)
  let refine_intvl_with_sign intvl sign =
    let intvl_of_sign = function
      | Sbot -> Ibot
      | Stop -> Itop
      | Neg -> Intvl (Ninf, Interval.Util.neg (Z Z.one))
      | Pos -> Intvl (Z Z.one, Pinf)
      | Nul -> Intvl (Z Z.zero, Z Z.zero)
    in let refined_intvl = Interval.meet (intvl_of_sign sign) intvl in
    if Interval.leq refined_intvl intvl && refined_intvl <> Ibot then refined_intvl else intvl
  in
  match p with
  | Prd { intvl; sign; congr } -> Prd {
      intvl = refine_intvl_with_congr (refine_intvl_with_sign intvl sign) congr;
      sign; congr
    }
  | _ -> Pbot

let unary p op =
  let p' =
    match p with
    | Prd p -> Prd {
        intvl = Interval.unary p.intvl op;
        sign = Sign.unary p.sign op;
        congr = Congruence.unary p.congr op;
      }
    | Pbot -> Pbot
  in refine p' (* seems useless to refine here but why not *)

let binary lhs rhs op =
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs -> Prd {
        intvl = Interval.binary lhs.intvl rhs.intvl op;
        sign = Sign.binary lhs.sign rhs.sign op;
        congr = Congruence.binary lhs.congr rhs.congr op;
      }
    | _ -> Pbot (* should bottom strictness hold for the product domain ? (i think so) *)
  in refine p

let compare lhs rhs op =
  let ic = Interval.compare and sc = Sign.compare and cc = Congruence.compare in
  match
    (match lhs, rhs with
    | Prd lhs, Prd rhs -> Some (
        ic lhs.intvl rhs.intvl op, sc rhs.sign rhs.sign op, cc lhs.congr rhs.congr op)
    | Pbot, Prd p -> Some (ic Ibot p.intvl op, sc Sbot p.sign op, cc Cbot p.congr op)
    | Prd p, Pbot -> Some (ic p.intvl Ibot op, sc p.sign Sbot op, cc p.congr Cbot op)
    | Pbot, Pbot -> None)
  with
  | Some ((a, b), (c, d), (e, f)) ->
      Prd { intvl = a; sign = c; congr = e }, Prd { intvl = b; sign = d; congr = f }
  | None -> Pbot, Pbot

let join lhs rhs =
  let ij = Interval.join and sj = Sign.join and cj = Congruence.join in
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs -> Prd {
        intvl = ij lhs.intvl rhs.intvl; 
        sign = sj lhs.sign rhs.sign; 
        congr = cj lhs.congr rhs.congr;
      }
    | Pbot, Prd p | Prd p, Pbot ->
        Prd { intvl = ij Ibot p.intvl; sign = sj Sbot p.sign; congr = cj Cbot p.congr }
    | Pbot, Pbot -> Pbot
  in refine p

let meet lhs rhs =
  let im = Interval.meet and sm = Sign.meet and cm = Congruence.meet in
  let p =
    match lhs, rhs with
    | Prd lhs, Prd rhs -> Prd {
        intvl = im lhs.intvl rhs.intvl;
        sign = sm lhs.sign rhs.sign;
        congr = cm lhs.congr rhs.congr;
      }
    | Pbot, Prd p | Prd p, Pbot ->
        Prd { intvl = im Ibot p.intvl; sign = sm Sbot p.sign; congr = cm Cbot p.congr }
    | Pbot, Pbot -> Pbot
  in refine p

(* I directly implemented the formula given in class : x_n+1 = widen x_n (rho (F# x_n)).
   I refine the right operand, assuming that it corresponds to F#(x_n) and I do not
   refine after widening *)
let widen lhs rhs =
  let rhs' = refine rhs in
  match lhs, rhs' with
  | _, Pbot -> Pbot
  | Pbot, _ -> rhs'
  | Prd lhs, Prd rhs -> Prd {
      intvl = Interval.widen lhs.intvl rhs.intvl;
      sign = Sign.widen lhs.sign rhs.sign;
      congr = Congruence.widen lhs.congr rhs.congr;
    }

let narrow lhs rhs = failwith "todo"

let leq lhs rhs =
  match lhs, rhs with
  | Pbot, _ -> true
  | Prd _, Pbot -> false
  | Prd lhs, Prd rhs ->
         Interval.leq lhs.intvl rhs.intvl
      && Sign.leq lhs.sign rhs.sign
      && Congruence.leq lhs.congr rhs.congr

let bwd_unary _ _ _ = failwith "todo"

let bwd_binary _ _ _ _ = failwith "todo"

let is_bottom = (=) Pbot

let pp fmt p =
    match p with
    | Pbot -> Format.fprintf fmt "bottom"
    | Prd { intvl; sign; congr } -> begin
        Format.fprintf fmt "{";
        Interval.pp fmt intvl;
        Sign.pp fmt sign;
        Congruence.pp fmt congr;
        Format.fprintf fmt "}"
      end
