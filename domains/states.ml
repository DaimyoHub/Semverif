(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* Abstract states types provider to avoid cyclic dependencies in the source code *)

(* Interval abstract state's type *)
type extended_z = Z of Z.t | Pinf | Ninf
type intvl = Intvl of extended_z * extended_z | Ibot | Itop

(* Sign abstract state's type *)
type sign = Stop | Sbot | Pos | Neg | Nul

(* Congruence abstract state's type *)
type congr = Cbot | Ctop | Cgr of int * int

(* Reduced product abstract state's type *)
type prod = Prd of { intvl : intvl; sign : sign; congr : congr } | Pbot
