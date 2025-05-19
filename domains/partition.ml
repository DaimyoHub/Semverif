module Key =
 struct
  module U = Map.Make (String)
  type t = bool U.t

  let compare = U.compare Bool.compare
  let empty = U.empty
 end

module Make (D : Domain.DOMAIN) =
 struct
  module Parts = Map.Make (Key)
  type t = D.t Parts.t

  module Util =
   struct
    let map2 f lhs rhs =
      Parts.fold
        (fun key part res ->
          Parts.add key
            (match Parts.find_opt key rhs with Some b -> f part b | None -> part) res)
        lhs Parts.empty
   end

  let key = let k = ref Key.empty in fun () -> k
  let get_key = !(key ())

  let add_boolean_condtion var value = key () := Key.U.add var value get_key
  let remove_boolean_condition var value = key () := Key.U.remove var get_key

  let screenshot_environment parts var value =
    Parts.add (Key.U.add var value get_key) (Parts.find get_key parts) parts
  
  let guard parts expr =
    Parts.add get_key (D.guard (Parts.find get_key parts) expr) parts

  let get_current_partition (parts : t) = Parts.find get_key parts

  let init = Parts.add Key.empty D.init Parts.empty
  let bottom = Parts.empty
  let assign parts var expr = Parts.map (fun part -> D.assign part var expr) parts
  let join = Util.map2 D.join
  let meet = Util.map2 D.meet
  let widen = Util.map2 D.widen
  let narrow = Util.map2 D.narrow
  let is_bottom = Parts.is_empty

  let leq lhs rhs = 
    Parts.fold
      (fun key part res ->
        match Parts.find_opt key rhs with
        | Some p -> res && (D.leq part p)
        | None -> res)
      lhs true

  let pp fmt parts =
    print_endline "{\n";
    Parts.iter
      (fun key part ->
        (Key.U.iter
          (fun var value ->
            Format.fprintf fmt "%s: %s; " var (if value then "1" else "0"))) key;
        print_endline "";
        D.pp fmt part)
      parts;
 end
