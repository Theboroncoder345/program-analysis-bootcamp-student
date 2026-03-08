(* ----------------------------------------------------------------
   Provided: Parse helper and main driver
   ---------------------------------------------------------------- *)

(** [parse_string s] parses the string [s] into an expr. *)
let parse_string (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  Parser.program Lexer.token lexbuf

(** [test_expr s] parses, prints, and evaluates the expression. *)
let test_expr (s : string) : unit =
  Printf.printf "Input:  %s\n" s;
  let e = parse_string s in
  Printf.printf "AST:    %s\n" (string_of_expr e);
  (match eval e with
   | Some n -> Printf.printf "Result: %d\n" n
   | None   -> Printf.printf "Result: <cannot evaluate>\n");
  Printf.printf "\n"

let () =
  Printf.printf "=== Exercise 5: Calculator Parser ===\n\n";

  test_expr "42";
  test_expr "1 + 2";
  test_expr "3 * 4 + 5";
  test_expr "(3 + 4) * 5";
  test_expr "10 - 3 - 2";
  test_expr "-7";
  test_expr "x + 1";

  Printf.printf "Done!\n"
