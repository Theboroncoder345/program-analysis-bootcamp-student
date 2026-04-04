(** CFG Construction Exercises.

    Each function below takes a list of AST statements and returns a CFG
    whose shape matches a specific control-flow pattern.

    Students: implement the functions marked with TODO.

    General approach for each exercise:
    1. Create the basic blocks with [Cfg.create_block].
    2. Put them into a [Cfg.StringMap] keyed by label.
    3. Build the initial [Cfg.cfg] record with entry, exit_label, and blocks.
    4. Use [Cfg.add_edge] to wire up the control flow edges.

    The ENTRY and EXIT blocks are always empty (no statements). *)

open Shared_ast.Ast_types

(** Build a CFG for straight-line (sequential) code.

    Expected shape:

      ENTRY --> B1 --> EXIT

    All statements go into a single block B1.

    Example input:
      [ Assign ("x", IntLit 1);
        Assign ("y", IntLit 2);
        Assign ("z", BinOp (Add, Var "x", Var "y")) ]

    @param stmts  A flat list of statements with no branches or loops. *)
let build_cfg_sequential (stmts : stmt list) : Cfg.cfg =
  (* Create blocks *)
  let entry = Cfg.create_block "ENTRY" [] in
  let b1    = Cfg.create_block "B1" stmts in
  let exit  = Cfg.create_block "EXIT" [] in

  (* Build map *)
  let blocks =
    Cfg.StringMap.empty
    |> Cfg.StringMap.add "ENTRY" entry
    |> Cfg.StringMap.add "B1" b1
    |> Cfg.StringMap.add "EXIT" exit
  in

  (* Initial CFG *)
  let cfg = { Cfg.entry = "ENTRY"; exit_label = "EXIT"; blocks } in

  (* Wire edges *)
  cfg
  |> Cfg.add_edge "ENTRY" "B1"
  |> Cfg.add_edge "B1" "EXIT"


(** Build a CFG for an if-else branch.

    Expected shape (diamond):

           ENTRY
             |
           B_cond
           /    \
       B_then  B_else
           \    /
           B_join
             |
            EXIT

    The input should contain statements before the if, the if-else
    itself, and statements after the if.

    The condition block B_cond holds any statements that precede the
    If, plus the If statement acts as the branch (but is not placed
    in a block -- only its children are).

    For simplicity, this exercise expects the input to be:
      [ ...pre-if stmts...;
        If (cond, then_stmts, else_stmts);
        ...post-if stmts... ]

    Map them to blocks:
    - B_cond : statements before the If
    - B_then : then_stmts
    - B_else : else_stmts
    - B_join : statements after the If

    @param stmts  Statement list containing exactly one If statement. *)
let build_cfg_ifelse (stmts : stmt list) : Cfg.cfg =
  (* Partition stmts around the If *)
  let rec split acc = function
    | [] -> failwith "Expected exactly one If statement"
    | If (cond, then_s, else_s) :: rest ->
        (List.rev acc, cond, then_s, else_s, rest)
    | s :: tl -> split (s :: acc) tl
  in
  let (pre, _cond, then_stmts, else_stmts, post) = split [] stmts in

  (* Create blocks *)
  let entry  = Cfg.create_block "ENTRY" [] in
  let bcond  = Cfg.create_block "B_cond" pre in
  let bthen  = Cfg.create_block "B_then" then_stmts in
  let belse  = Cfg.create_block "B_else" else_stmts in
  let bjoin  = Cfg.create_block "B_join" post in
  let exit   = Cfg.create_block "EXIT" [] in

  (* Build map *)
  let blocks =
    Cfg.StringMap.empty
    |> Cfg.StringMap.add "ENTRY" entry
    |> Cfg.StringMap.add "B_cond" bcond
    |> Cfg.StringMap.add "B_then" bthen
    |> Cfg.StringMap.add "B_else" belse
    |> Cfg.StringMap.add "B_join" bjoin
    |> Cfg.StringMap.add "EXIT" exit
  in

  (* Initial CFG *)
  let cfg = { Cfg.entry = "ENTRY"; exit_label = "EXIT"; blocks } in

  (* Wire edges *)
  cfg
  |> Cfg.add_edge "ENTRY" "B_cond"
  |> Cfg.add_edge "B_cond" "B_then"
  |> Cfg.add_edge "B_cond" "B_else"
  |> Cfg.add_edge "B_then" "B_join"
  |> Cfg.add_edge "B_else" "B_join"
  |> Cfg.add_edge "B_join" "EXIT"


(** Build a CFG for a while loop.

    Expected shape:

       ENTRY
         |
       B_pre       (statements before the while)
         |
       B_cond  <---+
       /    \      |
    B_body   \     |
      |       \    |
      +--------+   |
               |
            B_post  (statements after the while)
               |
             EXIT

    More precisely:
      ENTRY -> B_pre -> B_cond -> B_body -> B_cond  (back edge!)
                                  B_cond -> B_post -> EXIT

    @param stmts  Statement list containing exactly one While statement. *)
let build_cfg_while (stmts : stmt list) : Cfg.cfg =
  (* Partition stmts around the While *)
  let rec split acc = function
    | [] -> failwith "Expected exactly one While statement"
    | While (cond, body) :: rest ->
        (List.rev acc, cond, body, rest)
    | s :: tl -> split (s :: acc) tl
  in
  let (pre, _cond, body_stmts, post) = split [] stmts in

  (* Create blocks *)
  let entry = Cfg.create_block "ENTRY" [] in
  let bpre  = Cfg.create_block "B_pre" pre in
  let bcond = Cfg.create_block "B_cond" [] in
  let bbody = Cfg.create_block "B_body" body_stmts in
  let bpost = Cfg.create_block "B_post" post in
  let exit  = Cfg.create_block "EXIT" [] in

  (* Build map *)
  let blocks =
    Cfg.StringMap.empty
    |> Cfg.StringMap.add "ENTRY" entry
    |> Cfg.StringMap.add "B_pre" bpre
    |> Cfg.StringMap.add "B_cond" bcond
    |> Cfg.StringMap.add "B_body" bbody
    |> Cfg.StringMap.add "B_post" bpost
    |> Cfg.StringMap.add "EXIT" exit
  in

  (* Initial CFG *)
  let cfg = { Cfg.entry = "ENTRY"; exit_label = "EXIT"; blocks } in

  (* Wire edges *)
  cfg
  |> Cfg.add_edge "ENTRY" "B_pre"
  |> Cfg.add_edge "B_pre" "B_cond"
  |> Cfg.add_edge "B_cond" "B_body"   (* loop body *)
  |> Cfg.add_edge "B_cond" "B_post"   (* loop exit *)
  |> Cfg.add_edge "B_body" "B_cond"   (* back edge *)
  |> Cfg.add_edge "B_post" "EXIT"
