(* 
   Semantics and Applications to Verification course's project
   École Normale Supérieur

   Authors : 
     - Ilian Woerly : ilian.woerly@universite-paris-saclay.fr
     - Alexis Pocquet : alexis.pocquet@universite-paris-saclay.fr
 *)

(* Some tests to check if some parts of the implementation checks what is given in the
   course or in the given resources *)

open Frontend.AbstractSyntax
open Frontend.ControlFlowGraph
open States

(* Checking soundness of binary operation PLUS on the sign domain *)
let%test "sign_plus_pos" =
  let open Sign in
     binary Pos Pos AST_PLUS  = Pos
  && binary Pos Neg AST_PLUS  = Stop
  && binary Pos Nul AST_PLUS  = Pos
  && binary Pos Stop AST_PLUS = Stop
  && binary Pos Sbot AST_PLUS = Sbot

let%test "sign_plus_neg" =
  let open Sign in
     binary Neg Pos AST_PLUS  = Stop
  && binary Neg Neg AST_PLUS  = Neg
  && binary Neg Nul AST_PLUS  = Neg
  && binary Neg Stop AST_PLUS = Stop
  && binary Neg Sbot AST_PLUS = Sbot

let%test "sign_plus_nul" =
  let open Sign in
     binary Nul Pos AST_PLUS  = Pos
  && binary Nul Neg AST_PLUS  = Neg
  && binary Nul Nul AST_PLUS  = Nul
  && binary Nul Stop AST_PLUS = Stop
  && binary Nul Sbot AST_PLUS = Sbot

let%test "sign_plus_top" =
  let open Sign in
     binary Stop Pos AST_PLUS  = Stop
  && binary Stop Neg AST_PLUS  = Stop
  && binary Stop Nul AST_PLUS  = Stop
  && binary Stop Stop AST_PLUS = Stop
  && binary Stop Sbot AST_PLUS = Sbot

let%test "sign_plus_bot" =
  let open Sign in
     binary Sbot Pos AST_PLUS  = Sbot
  && binary Sbot Neg AST_PLUS  = Sbot
  && binary Sbot Nul AST_PLUS  = Sbot
  && binary Sbot Stop AST_PLUS = Sbot
  && binary Sbot Sbot AST_PLUS = Sbot

(* Checking soundness of binary operation MULTIPLY on the sign domain *)
let%test "sign_times_pos" =
  let open Sign in
     binary Pos Pos AST_MULTIPLY  = Pos
  && binary Pos Neg AST_MULTIPLY  = Neg
  && binary Pos Nul AST_MULTIPLY  = Nul
  && binary Pos Stop AST_MULTIPLY = Stop
  && binary Pos Sbot AST_MULTIPLY = Sbot

let%test "sign_times_neg" =
  let open Sign in
     binary Neg Pos AST_MULTIPLY  = Neg
  && binary Neg Neg AST_MULTIPLY  = Pos
  && binary Neg Nul AST_MULTIPLY  = Nul
  && binary Neg Stop AST_MULTIPLY = Stop
  && binary Neg Sbot AST_MULTIPLY = Sbot

let%test "sign_times_nul" =
  let open Sign in
     binary Nul Pos AST_MULTIPLY  = Nul
  && binary Nul Neg AST_MULTIPLY  = Nul
  && binary Nul Nul AST_MULTIPLY  = Nul
  && binary Nul Stop AST_MULTIPLY = Nul
  && binary Nul Sbot AST_MULTIPLY = Sbot

let%test "sign_times_top" =
  let open Sign in
     binary Stop Pos AST_MULTIPLY  = Stop
  && binary Stop Neg AST_MULTIPLY  = Stop
  && binary Stop Nul AST_MULTIPLY  = Nul
  && binary Stop Stop AST_MULTIPLY = Stop
  && binary Stop Sbot AST_MULTIPLY = Sbot

let%test "sign_times_bot" =
  let open Sign in
     binary Sbot Pos AST_MULTIPLY  = Sbot
  && binary Sbot Neg AST_MULTIPLY  = Sbot
  && binary Sbot Nul AST_MULTIPLY  = Sbot
  && binary Sbot Stop AST_MULTIPLY = Sbot
  && binary Sbot Sbot AST_MULTIPLY = Sbot

(* Checking soundness of binary operation DIVIDE on the sign domain *)
let%test "sign_divide_pos" =
  let open Sign in
     binary Pos Pos AST_DIVIDE  = Pos
  && binary Pos Neg AST_DIVIDE  = Neg
  && binary Pos Nul AST_DIVIDE  = Sbot
  && binary Pos Stop AST_DIVIDE = Stop
  && binary Pos Sbot AST_DIVIDE = Sbot

let%test "sign_divide_neg" =
  let open Sign in
     binary Neg Pos AST_DIVIDE  = Neg
  && binary Neg Neg AST_DIVIDE  = Pos
  && binary Neg Nul AST_DIVIDE  = Sbot
  && binary Neg Stop AST_DIVIDE = Stop
  && binary Neg Sbot AST_DIVIDE = Sbot

let%test "sign_divide_nul" =
  let open Sign in
     binary Nul Pos AST_DIVIDE  = Nul
  && binary Nul Neg AST_DIVIDE  = Nul
  && binary Nul Nul AST_DIVIDE  = Sbot
  && binary Nul Stop AST_DIVIDE = Nul
  && binary Nul Sbot AST_DIVIDE = Sbot

let%test "sign_divide_top" =
  let open Sign in
     binary Stop Pos AST_DIVIDE  = Stop
  && binary Stop Neg AST_DIVIDE  = Stop
  && binary Stop Nul AST_DIVIDE  = Sbot
  && binary Stop Stop AST_DIVIDE = Stop
  && binary Stop Sbot AST_DIVIDE = Sbot

let%test "sign_divide_bot" =
  let open Sign in
     binary Sbot Pos AST_DIVIDE  = Sbot
  && binary Sbot Neg AST_DIVIDE  = Sbot
  && binary Sbot Nul AST_DIVIDE  = Sbot
  && binary Sbot Stop AST_DIVIDE = Sbot
  && binary Sbot Sbot AST_DIVIDE = Sbot

(* Checking the product's refinement function *)
let%test "refine_with_sign_and_congr_top" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-1)) Z.one;
      sign = Neg;
      congr = Ctop;
    })
  in match ref with
  | Prd p -> p.intvl = Interval.const (Z.of_int (-1))
  | _ -> false

let%test "refine_with_congr_and_sign_top" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-3)) (Z.of_int 3);
      sign = Stop;
      congr = Cgr (2, 0);
    })
  in match ref with
  | Prd p -> p.intvl = Interval.rand (Z.of_int (-2)) (Z.of_int 2)
  | _ -> false

let%test "refine_with_sign_and_congr_bot" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-1)) Z.one;
      sign = Neg;
      congr = Cbot;
    })
  in match ref with
  | Prd p -> p.intvl = Interval.const (Z.of_int (-1))
  | _ -> false

let%test "refine_with_congr_and_sign_bot" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-3)) (Z.of_int 3);
      sign = Sbot;
      congr = Cgr (2, 0);
    })
  in match ref with
  | Prd p -> p.intvl = Interval.rand (Z.of_int (-2)) (Z.of_int 2)
  | _ -> false

let%test "refine_with_sign_and_congr" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-3)) (Z.of_int 3);
      sign = Neg;
      congr = Cgr (2, 0);
    })
  in match ref with
  | Prd p -> p.intvl = Interval.const (Z.of_int (-2))
  | _ -> false

let%test "refine_with_bot" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-1)) Z.one;
      sign = Sbot;
      congr = Cbot;
    })
  in
  match ref with
  | Prd p -> p.intvl = Interval.rand (Z.of_int (-1)) Z.one
  | _ -> false

let%test "refine_with_top" =
  let open Product in
  let ref = Product.refine (Prd {
      intvl = Interval.rand (Z.of_int (-1)) Z.one;
      sign = Stop;
      congr = Ctop;
    })
  in
  match ref with
  | Prd p -> p.intvl = Interval.rand (Z.of_int (-1)) Z.one
  | _ -> false
