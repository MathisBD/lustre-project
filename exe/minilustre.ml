(* Programme principal *)

open Format
open Lexing
open Lib

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] file.mls"
let main_node = ref ""
let verbose = ref false

let spec =
  [ ("-main", Arg.Set_string main_node, "<name>  main node")
  ; ("-verbose", Arg.Set verbose, "print intermediate transformations")
  ; ("-v", Arg.Set verbose, "print intermediate transformations")
  ]

let file =
  let file = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".mls") then raise (Arg.Bad "no .mls extension");
    file := Some s
  in
  Arg.parse spec set_file usage;
  match !file with
  | Some f -> f
  | None ->
      Arg.usage spec usage;
      exit 1

let report_loc (b, e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.file Lexer.token lb in
    close_in c;
    (* Type checking. *)
    let ft = Typing.type_file f !main_node in
    if !verbose
    then begin
      Format.printf "/**************************************/@.";
      Format.printf "/* Typed ast                          */@.";
      Format.printf "/**************************************/@.";
      Typed_ast_printer.print_node_list_std ft
    end;
    (* Normalization. *)
    (*let ft = Normalization.file ft in
    if !verbose
    then begin
      Format.printf "/**************************************/@.";
      Format.printf "/* Normalized ast                     */@.";
      Format.printf "/**************************************/@.";
      Typed_ast_printer.print_node_list_std ft
    end;
    Checks.normalization ft;*)
    (* Scheduling. *)
    let ft = Scheduling.schedule ft in
    if !verbose
    then begin
      Format.printf "/**************************************/@.";
      Format.printf "/* Scheduled ast                      */@.";
      Format.printf "/**************************************/@.";
      Typed_ast_printer.print_node_list_std ft
    end;
    Checks.scheduling ft;
    (* Initialization checking. *)
    Initialization.check ft;
    exit 0
  with
  | Lexer.Lexical_error s ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error: %s\n@." s;
      exit 1
  | Parsing.Parse_error ->
      report_loc (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "syntax error\n@.";
      exit 1
  | Typing.Error (l, e) ->
      report_loc l;
      eprintf "%a\n@." Typing.report e;
      exit 1
  | Initialization.InitializationError e ->
      report_loc e.texpr_loc;
      eprintf "the following expression is not well initialized : %a\n@."
        Typed_ast_printer.print_exp e;
      exit 1
  | e ->
      eprintf "Anomaly: %s\n@." (Printexc.to_string e);
      exit 2
