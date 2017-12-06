open preamble stringTheory
     lexer_funTheory lexer_implTheory
     cmlParseTheory
     inferTheory;

val _ = new_theory"compiler";

val _ = Datatype`compile_error = ParseError | TypeError mlstring | CompileError`;

val compile_to_javascript_def = Define `
  compile_to_javascript prog = SOME prog`;

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

val inferencer_config = ``<| inf_decls := empty_inf_decls ; inf_env := (<|inf_v := nsEmpty; inf_c := nsEmpty ; inf_t := nsEmpty |>)|>``;

val compile_def = Define `
  compile input =
    case parse_prog (lexer_fun input) of
      | NONE => Failure ParseError
      | SOME prog =>
          case infertype_prog ^(inferencer_config) prog of
            | Failure (locs, msg) =>
                Failure (TypeError (concat [msg; implode " at "; locs_to_string locs]))
            | Success _ =>
                case compile_to_javascript prog of
                  | NONE => Failure CompileError
                  | SOME ast => Success ast`;

val _ = export_theory();

``compile "val _ = ();"`` |> EVAL;
``compile "val _ = 5 + 5;"`` |> EVAL;
``compile "val _ = F;"`` |> EVAL;
``compile "val _ = F ==> T;"`` |> EVAL;
``compile "val _ = Define `foo bar = bar + 1`;"`` |> EVAL;

