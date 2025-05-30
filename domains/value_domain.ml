(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(* Signature of abstract domains representing sets of integers (for instance: constants
   or intervals) *)

open Frontend
open AbstractSyntax

module type VALUE_DOMAIN = sig
  (* type of abstract elements *)
  (* an element of type t abstracts a set of integers *)
  type t

  (* unrestricted value: [-oo,+oo] *)
  val top : t

  (* bottom value: empty set *)
  val bottom : t

  (* constant: {c} *)
  val const : Z.t -> t

  (* interval: [a,b] *)
  val rand : Z.t -> Z.t -> t

  (* unary operation *)
  val unary : t -> int_unary_op -> t

  (* binary operation *)
  val binary : t -> t -> int_binary_op -> t

  (* comparison *)
  (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
  val compare : t -> t -> compare_op -> t * t

  (* backards unary operation *)
  (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
  val bwd_unary : t -> int_unary_op -> t -> t

  (* backward binary operation *)
  (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
  val bwd_binary : t -> t -> int_binary_op -> t -> t * t

  (* set-theoretic operations *)
  val join : t -> t -> t

  val meet : t -> t -> t

  (* widening *)
  val widen : t -> t -> t

  (* narrowing *)
  val narrow : t -> t -> t

  (* subset inclusion of concretizations *)
  val leq : t -> t -> bool

  (* check the emptiness of the concretization *)
  val is_bottom : t -> bool

  (* print abstract element *)
  val pp : Format.formatter -> t -> unit
end

module type PARTIAL_VALUE_DOMAIN =
  sig
  (* type of abstract elements *)
  (* an element of type t abstracts a set of integers *)
  type t

  (* unrestricted value: [-oo,+oo] *)
  val top : t

  (* bottom value: empty set *)
  val bottom : t

  (* constant: {c} *)
  val const : Z.t -> t

  (* interval: [a,b] *)
  val rand : Z.t -> Z.t -> t

  (* unary operation *)
  val unary : t -> int_unary_op -> t

  (* binary operation *)
  val binary : t -> t -> int_binary_op -> t

  val compare : t -> t -> compare_op -> t * t
  
  val join : t -> t -> t

  val meet : t -> t -> t

  (* widening *)
  val widen : t -> t -> t

  (* narrowing *)
  val narrow : t -> t -> t

  (* subset inclusion of concretizations *)
  val leq : t -> t -> bool

  (* check the emptiness of the concretization *)
  val is_bottom : t -> bool

  (* print abstract element *)
  val pp : Format.formatter -> t -> unit
end
    

module Make (D : PARTIAL_VALUE_DOMAIN) : VALUE_DOMAIN with type t = D.t  =
  struct
    include D
    
    let bwd_unary x op z = D.unary z op
    
    let bwd_binary x y op z = match op with
      | AST_PLUS -> D.binary z x (AST_MINUS), D.binary z y (AST_MINUS)
      | AST_MINUS -> D.binary z x (AST_PLUS), D.binary z y (AST_PLUS)
      | AST_MULTIPLY -> D.binary z x (AST_DIVIDE), D.binary z y (AST_DIVIDE)
      | AST_DIVIDE ->
         (* si x / y = z alors
            x = z*y et, y = 0 ou y = x/z, à arondissement près
         *)
         let round = D.rand (Z.neg (Z.one)) Z.one in
         let z = D.binary z round AST_PLUS in
         D.binary z x (AST_MULTIPLY)
         ,
         D.binary
           (D.binary x z (AST_DIVIDE))
           (D.const (Z.zero))
           AST_PLUS
      | AST_MODULO -> assert false (* TODO *) 
  end

