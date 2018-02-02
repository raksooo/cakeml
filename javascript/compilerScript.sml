open preamble errorHandlingTheory
     lexer_funTheory lexer_implTheory cmlParseTheory
		 javascriptBackendTheory
		 prettyPrintTheory;
(* inferTheory *)

val _ = new_theory"compiler";

val to_cakeml_ast_def = Define `to_cakeml_ast input = parse_prog (lexer_fun input)`;

val compile_def = Define `compile input = OPTION_JOIN (OPTION_MAP ast_to_ast (to_cakeml_ast input))`;

val compile_pretty_def = Define `compile_pretty input = OPTION_MAP prog_toString (compile input)`;

val _ = export_theory();

