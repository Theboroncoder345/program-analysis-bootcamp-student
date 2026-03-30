(* visitor.ml - AST visitor pattern exercises.
   Implement two common visitor-style operations that walk the AST
   and accumulate information. *)

open Shared_ast.Ast_types

(** Count the number of each node type in a statement list.
    Returns an association list like:
      [("Assign", 3); ("IntLit", 5); ("BinOp", 2); ...]
    The keys are constructor names WITHOUT parameters (e.g., "IntLit"
    not "IntLit(3)"). Order does not matter.

    Hint:
      - Write recursive helpers for expr and stmt.
      - Use a mutable Hashtbl or a ref to a Map to accumulate counts,
        or thread an accumulator through the recursion.
      - Don't forget to count the node itself AND recurse into its
        children. *)
let count_nodes (stmts : stmt list) : (string * int) list =
  let tbl = Hashtbl.create 32 in

  let bump key =
    Hashtbl.replace tbl key
      (1 + (if Hashtbl.mem tbl key then Hashtbl.find tbl key else 0))
  in

  let rec visit_expr e =
    match e with
    | IntLit _ ->
        bump "IntLit"

    | BoolLit _ ->
        bump "BoolLit"

    | Var _ ->
        bump "Var"

    | BinOp (_, e1, e2) ->
        bump "BinOp";
        visit_expr e1;
        visit_expr e2

    | UnaryOp (_, e1) ->
        bump "UnaryOp";
        visit_expr e1

    | Call (_, args) ->
        bump "Call";
        List.iter visit_expr args
  in

  let rec visit_stmt s =
    match s with
    | Assign (_, e) ->
        bump "Assign";
        visit_expr e

    | If (cond, t, f) ->
        bump "If";
        visit_expr cond;
        List.iter visit_stmt t;
        List.iter visit_stmt f

    | While (cond, body) ->
        bump "While";
        visit_expr cond;
        List.iter visit_stmt body

    | Return opt ->
        bump "Return";
        (match opt with
         | Some e -> visit_expr e
         | None -> ())

    | Print exprs ->
        bump "Print";
        List.iter visit_expr exprs

    | Block stmts ->
        bump "Block";
        List.iter visit_stmt stmts
  in

  List.iter visit_stmt stmts;

  Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl []
(** Evaluate a constant expression, returning Some int if the
    expression contains only integer literals and arithmetic operators,
    or None if it contains variables, booleans, calls, or comparison
    operators.

    Supported operators: Add, Sub, Mul, Div (integer division).
    Division by zero should return None.

    Examples:
      evaluate (IntLit 42)                        => Some 42
      evaluate (BinOp (Add, IntLit 1, IntLit 2))  => Some 3
      evaluate (BinOp (Add, IntLit 1, Var "x"))   => None
      evaluate (BoolLit true)                      => None

    Hint: use Option.bind or match on recursive results. *)
let evaluate (e : expr) : int option =
  match e with
  | IntLit n -> Some n

  | BoolLit _ -> None
  | Var _ -> None

  | BinOp (op, e1, e2) ->
      (match evaluate e1, evaluate e2 with
       | Some v1, Some v2 ->
           (match op with
            | Add -> Some (v1 + v2)
            | Sub -> Some (v1 - v2)
            | Mul -> Some (v1 * v2)
            | Div ->
                if v2 = 0 then None else Some (v1 / v2)
            | _ -> None)
       | _ -> None)

  | UnaryOp (_, e1) ->
      (match evaluate e1 with
       | Some v -> Some (-v)
       | None -> None)

  | Call _ ->
      None
