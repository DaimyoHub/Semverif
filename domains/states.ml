(* Interval abstract state's type *)
type extended_z = Z of Z.t | Pinf | Ninf
type intvl = Intvl of extended_z * extended_z | Ibot | Itop

(* Sign abstract state's type *)
type sign = Stop | Sbot | Pos | Neg | Nul

(* Congruence abstract state's type *)
type congr = Cbot | Ctop | Mod of int

(* Reduced product abstract state's type *)
type prod = Prd of { intvl : intvl; sign : sign } | Pbot
