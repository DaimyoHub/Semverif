(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* Instanciations of modules that should be used by the iterator *)

open Domain

(* Value domains. They should not be used outside in the iterator *)
module Sign = Value_domain.Make (Sign)
module Interval = Value_domain.Make (Interval)
module Congruence = Value_domain.Make (Congruence)
module Product = Value_domain.Make (Product)

(* Non relational domains *)
module Make_nr_sign (V : VARS) = Non_relational.Make (Sign) (V)
module Make_nr_interval (V : VARS) = Non_relational.Make (Interval) (V)
module Make_nr_congruence (V : VARS) = Non_relational.Make (Congruence) (V)
module Make_nr_product (V : VARS) = Non_relational.Make (Product) (V)

(* Partitioning domains *)
module Make_part_sign (V : VARS) = Part.Make (Make_nr_sign (V))
module Make_part_interval (V : VARS) = Part.Make (Make_nr_interval (V))
module Make_part_congruence (V : VARS) = Part.Make (Make_nr_congruence (V))
module Make_part_product (V : VARS) = Part.Make (Make_nr_product (V))
