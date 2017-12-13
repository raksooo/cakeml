open preamble stringTheory
     lexer_funTheory lexer_implTheory
     cmlParseTheory inferTheory;
(* basisProgTheory *)

val _ = new_theory"compiler";

val _ = Datatype`compile_error = ParseError | TypeError mlstring | CompileError`;

val locs_to_string_def = Define `
  (locs_to_string NONE = implode "unknown location") /\
  (locs_to_string (SOME (Locs startl endl)) =
    if Locs startl endl = unknown_loc then
      implode "unknown location"
    else
      concat
        [implode "location starting at row ";
         toString &startl.row;
         implode " column ";
         toString &startl.col;
         implode ", ending at row ";
         toString &endl.row;
         implode " column ";
         toString &endl.col])`;

val error_to_str_def = Define`
  (error_to_str ParseError = strlit "### ERROR: parse error\n") /\
  (error_to_str (TypeError s) = concat [strlit "### ERROR: type error\n"; s; strlit "\n"]) /\
  (error_to_str CompileError = strlit "### ERROR: compile error\n")`;

val inferencer_config = ``<| inf_decls := empty_inf_decls ; inf_env := (<|inf_v := nsEmpty; inf_c := nsEmpty ; inf_t := nsEmpty |>)|>``;

val cakeml_to_javascript_def = Define `
  cakeml_to_javascript prog = SOME prog`;

val javascript_ast_to_source_def = Define `
  javascript_ast_to_source ast = "todo"`;

val compile_def = Define `
  compile inferencer_config prelude input =
    case parse_prog (lexer_fun input) of
      | NONE => Failure ParseError
      | SOME prog =>
          case infertype_prog inferencer_config (prelude ++ prog) of
            | Failure (locs, msg) =>
                Failure (TypeError (concat [msg; implode " at "; locs_to_string locs]))
            | Success _ =>
                case cakeml_to_javascript prog of
                  | NONE => Failure CompileError
                  | SOME ast => Success ast`;

val compile_to_javascript_def = Define `
  (*compile_to_javascript input = compile ^(inferencer_config) basis input`;*)
  compile_to_javascript input = case compile ^(inferencer_config) [] input of
    | Failure error => error_to_str error
    | Success ast => javascript_ast_to_source ast`;

val _ = export_theory();

``compile ""`` |> EVAL;
``compile "val _ = \"foo\";"`` |> EVAL;
``compile "val _ = ();"`` |> EVAL;
``compile "val _ = 5 + 5;"`` |> EVAL;
``compile "val _ = F;"`` |> EVAL;
``compile "val _ = F ==> T;"`` |> EVAL;
``compile "val _ = Define `foo bar = bar + 1`;"`` |> EVAL;

