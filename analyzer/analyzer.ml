(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend
open Domains.Roots
open Domains

module type VARS = Domain.VARS
module type DOMAIN = Domain.DOMAIN

let usage () = Arg.usage Options.args Options.usage; assert false

let parse_argv argv =
  let n = Array.length argv in
  let rec loop i =
    if i >= n then None
    else if argv.(i) = "--domain" then Some (argv.(i + 1)) else loop (i + 1)
  in
  loop 0

let parse_domain (module V : VARS) dom : (module DOMAIN) =
  if String.starts_with ~prefix: "part-" dom then
    match String.split_on_char '-' dom with
    | _ :: d :: [] -> 
      if d = "interval" then
        (module Make_part_interval (V))
      else if d = "congruence" then
        (module Make_part_congruence (V))
      else if d = "sign" then
        (module Make_part_sign (V))
      else if d = "product" then
        (module Make_part_product (V))
      else usage ()
    | _ -> usage ()
  else
    if dom = "interval" then
      (module Make_nr_interval (V))
    else if dom = "congruence" then
      (module Make_nr_congruence (V))
    else if dom = "sign" then
      (module Make_nr_sign (V))
    else if dom = "product" then
      (module Make_nr_product (V))
    else usage ()

let get_domain (module V : VARS) domains : (module DOMAIN) =
  match domains with
  | None -> (module Make_nr_product (V))
  | Some x -> parse_domain (module V) x

(* parse filename *)
let doit filename =
  let prog = FileParser.parse_file filename in
  let cfg = Tree_to_cfg.prog prog in
  if !Options.verbose then Format.printf "%a" ControlFlowGraphPrinter.print_cfg cfg ;
  ControlFlowGraphPrinter.output_dot !Options.cfg_out cfg ;

  let doms = parse_argv Sys.argv in
  let module V : VARS = struct let support = cfg.cfg_vars end in
  let (module Dom : DOMAIN) = get_domain (module V) doms in
  Iterator.iterate (module Dom) cfg

(* parses arguments to get filename *)
let main () =
  let _ = Options.init () in
  doit !Options.file

let _ = main ()

