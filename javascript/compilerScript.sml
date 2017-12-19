open preamble stringTheory
     basisProgTheory
     lexer_funTheory lexer_implTheory
     cmlParseTheory inferTheory inferenceComputeLib;
(*
     basisSubsetTheory
     std_preludeTheory
*)

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
         implode " character ";
         toString &startl.col;
         implode ", ending at row ";
         toString &endl.row;
         implode " character ";
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
  compile inf_conf prelude input =
    case parse_prog (lexer_fun input) of
      | NONE => Failure ParseError
      | SOME prog =>
          case infertype_prog inf_conf (prelude ++ prog) of
            | Failure (locs, msg) =>
                Failure (TypeError (concat [msg; implode " at "; locs_to_string locs]))
            | Success _ =>
                case cakeml_to_javascript prog of
                  | NONE => Failure CompileError
                  | SOME ast => Success ast`;

val compile_to_javascript_def = Define `
  compile_to_javascript input = case compile init_config basis input of
    | Failure error => error_to_str error
    | Success ast => strlit (javascript_ast_to_source ast)`;

val cakeml_src_to_ast_def = Define `
  cakeml_src_to_ast input = case compile init_config basis input of
    | Failure error => Failure (error_to_str error)
    | Success ast => Success ast`;

add_inference_compset computeLib.the_compset;

val _ = export_theory();

``cakeml_src_to_ast ""`` |> EVAL;
``cakeml_src_to_ast "val _ = \"foo\";"`` |> EVAL;
``cakeml_src_to_ast "val _ = ();"`` |> EVAL;
``cakeml_src_to_ast "val fivePlusFive = 5 + 5;"`` |> EVAL;
``cakeml_src_to_ast "val five = 5;"`` |> EVAL;
``cakeml_src_to_ast "val _ = lkljsdflkjsdflkjsjdfdlkj;"`` |> EVAL;
``cakeml_src_to_ast "val _ = F ==> T;"`` |> EVAL;
``cakeml_src_to_ast "val _ = Asdf `foo bar = bar + 1`;"`` |> EVAL;

computeLib.CBV_CONV

`val _ = ();` |> parse_topdecs;

