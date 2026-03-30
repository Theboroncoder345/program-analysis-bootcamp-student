(* traversals.ml - AST traversal algorithms exercise.
   Implement three classic tree traversal strategies on the AST:
   pre-order (depth-first), post-order (depth-first), and
   breadth-first (level-order).

   Each function walks a list of statements and collects a string label
   for every node visited. Labels should look like:
     Statements: "Assign", "If", "While", "Return", "Print", "Block"
     Expressions: "IntLit(3)", "BoolLit(true)", "Var(x)", "BinOp(+)",
                  "UnaryOp(-)", "Call(f)"
*)

open Shared_ast.Ast_types

(** Helper: produce a string label for a single expression node.
    Examples: IntLit(3), BoolLit(true), Var(x), BinOp(+), UnaryOp(-), Call(f) *)
let label_of_expr (e : expr) : string =
  match e with
  | IntLit n -> "IntLit(" ^ string_of_int n ^ ")"
  | BoolLit b -> "BoolLit(" ^ string_of_bool b ^ ")"
  | Var x -> "Var(" ^ x ^ ")"
  | BinOp (op, _, _) ->
      let op_str =
        match op with
        | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
        | Eq -> "==" | Neq -> "!=" | Lt -> "<" | Gt -> ">"
        | Le -> "<=" | Ge -> ">=" | And -> "&&" | Or -> "||"
      in
      "BinOp(" ^ op_str ^ ")"
  | UnaryOp (op, _) ->
      let op_str = match op with Neg -> "-" | Not -> "!" in
      "UnaryOp(" ^ op_str ^ ")"
  | Call (f, _) -> "Call(" ^ f ^ ")"

(** Helper: produce a string label for a single statement node.
    Examples: "Assign", "If", "While", "Return", "Print", "Block" *)
let label_of_stmt (s : stmt) : string =
  match s with
  | Assign _ -> "Assign"
  | If _ -> "If"
  | While _ -> "While"
  | Return _ -> "Return"
  | Print _ -> "Print"
  | Block _ -> "Block"

(** Pre-order depth-first traversal.
    Visit the current node FIRST, then recurse into its children
    left-to-right.

    For example, on [Assign("x", BinOp(Add, IntLit 1, IntLit 2))]:
      ["Assign"; "BinOp(+)"; "IntLit(1)"; "IntLit(2)"]

    Hint: write a mutual recursion with helpers for expr and stmt lists. *)
let rec pre_order (stmts : stmt list) : string list =
  let rec pre_expr e =
     match e with
     | IntLit _ | BoolLit _ | Var _ ->
         [label_of_expr e]
   
     | BinOp (_, e1, e2) ->
         label_of_expr e :: (pre_expr e1 @ pre_expr e2)
   
     | UnaryOp (_, e1) ->
         label_of_expr e :: pre_expr e1
   
     | Call (_, args) ->
         label_of_expr e :: List.flatten (List.map pre_expr args)
  in
  let rec pre_stmt s =
     match s with
     | Assign (_, e) ->
         label_of_stmt s :: pre_expr e
   
     | If (cond, t, f) ->
         label_of_stmt s ::
         (pre_expr cond
          @ List.flatten (List.map pre_stmt t)
          @ List.flatten (List.map pre_stmt f))
   
     | While (cond, body) ->
         label_of_stmt s ::
         (pre_expr cond @ List.flatten (List.map pre_stmt body))
   
     | Return None ->
         [label_of_stmt s]
   
     | Return (Some e) ->
         label_of_stmt s :: pre_expr e
   
     | Print exprs ->
         label_of_stmt s ::
         List.flatten (List.map pre_expr exprs)
   
     | Block stmts ->
         label_of_stmt s ::
         List.flatten (List.map pre_stmt stmts)
   in
   
   List.flatten (List.map pre_stmt stmts)
(** Post-order depth-first traversal.
    Recurse into children FIRST, then visit the current node.

    For example, on [Assign("x", BinOp(Add, IntLit 1, IntLit 2))]:
      ["IntLit(1)"; "IntLit(2)"; "BinOp(+)"; "Assign"]

    Hint: same structure as pre_order but emit the label at the end. *)
let post_order (stmts : stmt list) : string list =
  let rec post_expr e =
     match e with
     | IntLit _ | BoolLit _ | Var _ ->
         [label_of_expr e]
   
     | BinOp (_, e1, e2) ->
         post_expr e1 @ post_expr e2 @ [label_of_expr e]
   
     | UnaryOp (_, e1) ->
         post_expr e1 @ [label_of_expr e]
   
     | Call (_, args) ->
         List.flatten (List.map post_expr args) @ [label_of_expr e]
   in
   let rec post_stmt s =
     match s with
     | Assign (_, e) ->
         post_expr e @ [label_of_stmt s]
   
     | If (cond, t, f) ->
         post_expr cond
         @ List.flatten (List.map post_stmt t)
         @ List.flatten (List.map post_stmt f)
         @ [label_of_stmt s]
   
     | While (cond, body) ->
         post_expr cond
         @ List.flatten (List.map post_stmt body)
         @ [label_of_stmt s]
   
     | Return None ->
         [label_of_stmt s]
   
     | Return (Some e) ->
         post_expr e @ [label_of_stmt s]
   
     | Print exprs ->
         List.flatten (List.map post_expr exprs)
         @ [label_of_stmt s]
   
     | Block stmts ->
         List.flatten (List.map post_stmt stmts)
         @ [label_of_stmt s]
   in
   
   List.flatten (List.map post_stmt stmts)
(** Breadth-first (level-order) traversal.
    Visit all nodes at depth d before any node at depth d+1.

    For example, on [Assign("x", BinOp(Add, IntLit 1, IntLit 2))]:
      ["Assign"; "BinOp(+)"; "IntLit(1)"; "IntLit(2)"]
    (In this small case it happens to match pre-order, but differs on
     deeper trees with multiple siblings.)

    Hint: use the OCaml Queue module.
      1. Seed the queue with all top-level stmts.
      2. Dequeue a node, emit its label, enqueue its children.
      3. Repeat until the queue is empty.
    You will need a sum type or two queues to handle both stmt and expr
    nodes uniformly. *)
type node =
  | S of stmt
  | E of expr

let bfs (stmts : stmt list) : string list =
  let q = Queue.create () in
  List.iter (fun s -> Queue.add (S s) q) stmts;

  let acc = ref [] in

  while not (Queue.is_empty q) do
    match Queue.take q with
    | S s ->
        acc := label_of_stmt s :: !acc;
        (match s with
         | Assign (_, e) ->
             Queue.add (E e) q

         | If (cond, t, f) ->
             Queue.add (E cond) q;
             List.iter (fun x -> Queue.add (S x) q) t;
             List.iter (fun x -> Queue.add (S x) q) f

         | While (cond, body) ->
             Queue.add (E cond) q;
             List.iter (fun x -> Queue.add (S x) q) body

         | Return (Some e) ->
             Queue.add (E e) q

         | Return None -> ()

         | Print exprs ->
             List.iter (fun e -> Queue.add (E e) q) exprs

         | Block stmts ->
             List.iter (fun x -> Queue.add (S x) q) stmts)

    | E e ->
        acc := label_of_expr e :: !acc;
        (match e with
         | IntLit _ | BoolLit _ | Var _ -> ()

         | BinOp (_, e1, e2) ->
             Queue.add (E e1) q;
             Queue.add (E e2) q

         | UnaryOp (_, e1) ->
             Queue.add (E e1) q

         | Call (_, args) ->
             List.iter (fun e -> Queue.add (E e) q) args)
  done;

  List.rev !acc
