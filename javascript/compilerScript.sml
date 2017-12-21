open preamble basisProgTheory errorHandlingTheory
     lexer_funTheory lexer_implTheory
     cmlParseTheory inferTheory
		 javascriptBackendTheory;

val _ = new_theory"compiler";

val cakeml_to_javascript_def = Define `
  cakeml_to_javascript prog = SOME prog`;

val javascript_ast_to_source_def = Define `
  javascript_ast_to_source ast = "todo"`;

val compile_def = Define `
  compile inf_conf prelude input =
    case parse_prog (lexer_fun input) of
      | NONE => Failure ParseError
      | SOME prog =>
          case infertype_prog inf_conf (prelude ++ prog) of
            | Failure f => Failure (create_type_error f)
            | Success _ =>
                case cakeml_to_javascript prog of
                  | NONE => Failure CompileError
                  | SOME ast => Success ast`;

val compile_to_javascript_def = Define `
  compile_to_javascript input = case compile init_config basis input of
    | Failure error => Failure (error_to_str error)
    | Success ast => Success (ast_to_ast ast)`;

val cakeml_src_to_ast_def = Define `
  cakeml_src_to_ast input = case compile init_config basis input of
    | Failure error => Failure (error_to_str error)
    | Success ast => Success ast`;

val _ = export_theory();

