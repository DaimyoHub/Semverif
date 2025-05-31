(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* Partitioning domain's implementation *)

open Frontend.ControlFlowGraph
open Domain

(* The design of the partitioning domain is a bit dirty because I mixed functional
   features of a usual domain and the imperative features induced by the way I'm dealing
   with partitions and keys. *)
module Make (D : DOMAIN) : 
 sig
  include DOMAIN

  val add_bool_cond : t -> string -> unit
  val rm_bool_cond :  t -> string -> unit
  val get_curr_part : t -> D.t
  val split :         t -> string -> bool_expr -> unit
 end
  =
 struct
  type key = string list

  type t = {
    parts : (key, D.t) Hashtbl.t;
    mutable key : key
  }

  module Util =
   struct
    let map2 f tbl1 tbl2 =
      let tbl = Hashtbl.create 7 in
      Hashtbl.iter
        (fun key v1 ->
          match Hashtbl.find_opt tbl2 key with
          | Some v2 -> Hashtbl.add tbl key (f v1 v2)
          | None -> Hashtbl.add tbl key v1)
        tbl1;
      tbl

    module StrSet = Set.Make (String)

    let set_op_for_keys op key1 key2 = 
      let set1 = List.fold_left (fun acc x -> StrSet.add x acc) StrSet.empty key1 in
      let set2 = List.fold_left (fun acc x -> StrSet.add x acc) StrSet.empty key2 in
      StrSet.elements (op set1 set2)

    let key_or = set_op_for_keys StrSet.union
    let key_and = set_op_for_keys StrSet.inter
   end

  (* These functions should be used when passing through the condition of a conditional
     statement. For instance 

     if (b1) {            <-- add_bool_cond st "b1"
       if (!b2) {         <-- add_bool_cond st "b2"
         /* ... */    
       }                  <-- rm_bool_cond st "b2"
     }                    <-- rm_bool_cond st "b1"
     
     This allows to keep track of the key to access the good partition. *)
  let add_bool_cond state var = state.key <- var :: state.key
  let rm_bool_cond state var = state.key <- List.filter (fun v -> v <> var) state.key

  (* This function finds the partition associated with the current key. *)
  let get_curr_part state = Hashtbl.find state.parts state.key

  (* Splitting the partitions occurs when a new boolean variable is associated with a
     conditional expression. For instance

     bool b1 = x > 1;     <-- split st "b1" <x > 1>
     bool b2 = x == 1;    <-- split st "b2" <x == 1>

     In the first line, we create a partition in which the variable b1 is true and in 
     which we consider that x > 1. It works the same way for the second line.
   *)
  let split state var expr =
    let curr_part = Hashtbl.find state.parts state.key in
    Hashtbl.replace state.parts (var :: state.key) (D.guard curr_part expr)

  let guard state expr =
    let curr_part = Hashtbl.find state.parts state.key in
    Hashtbl.replace state.parts state.key (D.guard curr_part expr);
    state
  
  let assign state var expr : t =
    let parts = Hashtbl.create 7 in
    Hashtbl.iter
      (fun key part -> Hashtbl.add parts key (D.assign part var expr))
      state.parts;
    { state with parts }

  let init =
    let parts = Hashtbl.create 7 in Hashtbl.add parts [] D.init;
    { key = []; parts }

  let bottom = { key = []; parts = Hashtbl.create 7 }

  let join lhs rhs = {
    parts = Util.map2 D.join lhs.parts rhs.parts;
    key = Util.key_or lhs.key rhs.key }

  let meet lhs rhs = {
    parts = Util.map2 D.meet lhs.parts rhs.parts;
    key = Util.key_and lhs.key rhs.key }

  let widen lhs rhs = {
    parts = Util.map2 D.widen lhs.parts rhs.parts;
    key = Util.key_or lhs.key rhs.key }

  let narrow lhs rhs = {
    parts = Util.map2 D.narrow lhs.parts rhs.parts;
    key = Util.key_and lhs.key rhs.key }

  let is_bottom state = D.is_bottom @@ Hashtbl.find state.parts state.key

  let leq lhs rhs = 
    Hashtbl.fold
      (fun key part res ->
        match Hashtbl.find_opt rhs.parts key with
        | Some p -> res && (D.leq part p)
        | None -> res)
      lhs.parts true

  let pp fmt state =
    print_endline "{\n";
    Hashtbl.iter
      (fun key part ->
        List.iter (fun var -> Format.fprintf fmt "%s: %s; " var "1") key;
        print_endline "";
        D.pp fmt part)
      state.parts
 end

(*
   Full example : We consider a simple program in which the value of a variable x depends
   on the value of a boolean variable b.

   int x = rand(0, 100);
   bool b = x > 0;
   if (b) {
     assert(x != 0);
   }

   Without any partitioning domain, the analyzer fails to prove the assertion in the
   conditional statement.

   int x = rand(0, 100);
   bool b = x > 0;
   if (b) {
     assert(x != 0);      <-- KO because the analyzer does not compute the relation
   }                          between x and b

   With the partitioning domain implemented above, the goal is to be able to check this
   assertion, by considering partitions of the abstract state of x determined by the
   value of b. In other word, it should be able to compute invariants in conditional
   statements such that their condition is an indirection as a boolean variable to a 
   condition on the assertion's variables.

   int x = rand(0, 100);
   bool b = x > 0;
   if (b) {
     assert(x != 0);      <-- OK because the analyzer computes "b = true -> x > 0"
   }
 *)
