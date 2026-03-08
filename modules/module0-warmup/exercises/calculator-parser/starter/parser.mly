(* ================================================================
   Exercise 5: Calculator Parser -- Main Driver
   ================================================================

   This file reads expressions from built-in examples, parses them
   with the Menhir-generated parser, and prints + evaluates the
   resulting AST.

   TODO: Implement [string_of_op], [string_of_expr], and [eval].
   The parse + main driver code is provided.

   Run with:  dune exec modules/module0-warmup/exercises/calculator-parser/starter/main.exe
   ================================================================ *)

open Ast

(* ----------------------------------------------------------------
   Part 1: Pretty-Printing
   ---------------------------------------------------------------- *)

(** [string_of_op op] returns "+", "-", "*", or "/". *)
let string_of_op (o : op) : string =
  match o with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

(** [string_of_expr e] returns a fully parenthesized string.
    Examples:
      Num 3            --> "3"
      Var "x"          --> "x"
      Neg (Num 5)      --> "(- 5)"
      BinOp(Add, Num 1, Num 2)  --> "(1 + 2)" *)
let rec string_of_expr (e : expr) : string =
  match e with
  | Num n -> string_of_int n
  | Var x -> x
  | Neg e1 -> "(- " ^ string_of_expr e1 ^ ")"
  | BinOp (op, e1, e2) ->
      "(" ^ string_of_expr e1 ^ " " ^ string_of_op op ^ " " ^ string_of_expr e2 ^ ")"

(* ----------------------------------------------------------------
   Part 2: Evaluation
   ---------------------------------------------------------------- *)

(** [eval e] evaluates [e] if it contains no variables.
    Returns [Some n] on success, [None] if a Var is encountered.
    Division by zero returns [None]. *)
let rec eval (e : expr) : int option =
  match e with
  | Num n -> Some n
  | Var _ -> None
  | Neg e1 ->
      (match eval e1 with
       | Some n -> Some (-n)
       | None -> None)
  | BinOp (op, e1, e2) ->
      match eval e1, eval e2 with
      | Some v1, Some v2 ->
          (match op with
           | Add -> Some (v1 + v2)
           | Sub -> Some (v1 - v2)
           | Mul -> Some (v1 * v2)
           | Div ->
               if v2 = 0 then None else Some (v1 / v2))
      | _ -> None

