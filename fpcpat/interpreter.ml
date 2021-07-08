open! Core

let run ~filename ~type_checker () =
  let ast =
    In_channel.with_file filename ~f:(fun in_channel ->
      let lexbuf = Lexing.from_channel in_channel in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      Parser.program Lexer.token lexbuf)
  in
  let abt = Abt_of_ast.convert ast in
  printf "%s\n%!" (Abt.exp_to_string abt);
  (match type_checker with
   | `None -> ()
   | `Bidirectional ->
     printf "%s\n%!" (Abt.typ_to_string (Bidirectional_type_checker.typecheck_exn abt))
   | `Hindley_milner ->
     printf "%s\n%!" (Abt.typ_to_string (Hindley_milner_type_checker.typecheck_exn abt))
   | `Hindley_milner_with_rows ->
     printf "%s\n%!" (Abt.typ_to_string (Hindley_milner_with_rows.typecheck_exn abt)));
  printf "%s\n%!" (Abt.exp_to_string (Dynamics.eval abt))
;;

let type_checker_arg_type =
  Command.Arg_type.of_alist_exn
    [ ("none", `None)
    ; ("bidirectional", `Bidirectional)
    ; ("hindley-milner", `Hindley_milner)
    ; ("rows", `Hindley_milner_with_rows)
    ]
;;

let command =
  Command.basic
    ~summary:"Interprets fpcpat programs"
    (let%map_open.Command () = return ()
     and filename = anon ("FILE" %: Filename.arg_type)
     and type_checker =
       flag "type-checker" (required type_checker_arg_type)
         ~doc:" which type checker to use (none|bidirectional|hindley-milner)"
     in
     fun () -> run ~filename ~type_checker ())
;;
