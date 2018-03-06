open preamble lexer_funTheory lexer_implTheory cmlParseTheory
		 javascriptBackendTheory prettyPrintTheory
		 mlstringTheory;

val _ = new_theory"compiler";

val error_to_str_def = Define`
  (error_to_str ParseError = strlit "### ERROR: parse error\n") /\
  (error_to_str (TypeError s) = concat [strlit "### ERROR: type error\n"; s; strlit "\n"]) /\
  (error_to_str CompileError = strlit "### ERROR: compile error\n")`;

val to_cakeml_ast_def = Define `
	to_cakeml_ast input = parse_prog (lexer_fun input)`;

val compile_def = Define `
	compile input = OPTION_BIND (to_cakeml_ast input) ast_to_ast`;

val compile_pretty_def = Define `
	compile_pretty input = (OPTION_MAP prog_toString o compile) input`;

val main = process_topdecs`
	fun main u =
		let cl = CommandLine.arguments () in
			case compile_pretty cl of
				| NONE => TextIO.output "NONE"
				| SOME js => TextIO.output js`;

val _ = export_theory();

