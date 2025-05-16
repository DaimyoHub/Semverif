(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* The iterator should use this domain to compute abstract states of the program *)

include Non_relational.Make
  (Product)
  (struct let support = [] end)
