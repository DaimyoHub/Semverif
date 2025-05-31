open Frontend.ControlFlowGraph
open Domain

module Make (D : DOMAIN) : 
 sig
  include DOMAIN

  val add_bool_cond : string -> bool -> unit
  val rm_bool_cond : string -> unit
  val get_curr_part : t -> D.t
 end
  =
 struct
  type key = (string, bool) Hashtbl.t
  type t = (key, D.t) Hashtbl.t

  module Util =
   struct
    let map2 f lhs rhs =
      let r = Hashtbl.create 7 in
      Hashtbl.iter
        (fun key part ->
          Hashtbl.add r key (
            match Hashtbl.find_opt key rhs with
            | None -> part
            | Some p -> f part p))
        lhs;
      r
   end

  let key = Hashtbl.create 7

  (* These functions should be used when passing through the condition of a conditional
     statement. For instance 

     if (b1) {        <-- add_bool_cond b1 true
       if (!b2) {     <-- add_bool_cond b2 false
         /* ... */    
       }              <-- rm_bool_cond b2
     }                <-- rm_bool_cond b1
     
     This allows to keep track of the key to access the good partition. *)
  let add_bool_cond var value = Hashtbl.add key var value
  let rm_bool_cond var = Hashtbl.remove key var

  (* This function finds the partition associated with the current key. *)
  let get_curr_part parts = Hashtbl.find parts key

  let guard parts expr = failwith "todo"
  let init = let r = Hashtbl.create 7 in Hashtbl.add r key D.init; r
  let bottom = Hashtbl.create 7
  let assign parts var expr = Parts.map (fun part -> D.assign part var expr) parts
  let join = Util.map2 D.join
  let meet = Util.map2 D.meet
  let widen = Util.map2 D.widen
  let narrow = Util.map2 D.narrow
  let is_bottom = Parts.is_empty

  let leq lhs rhs = 
    Hashtbl.fold
      (fun key part res ->
        match Hashtbl.find_opt key rhs with
        | Some p -> res && (D.leq part p)
        | None -> res)
      lhs true

  let pp fmt parts =
    print_endline "{\n";
    Hashtbl.iter
      (fun key part ->
        (Hashtbl.iter
          (fun var value ->
            Format.fprintf fmt "%s: %s; " var (if value then "1" else "0"))) key;
        print_endline "";
        D.pp fmt part)
      parts;
 end
