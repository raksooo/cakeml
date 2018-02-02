open preamble inferTheory mlstringTheory;

val _ = new_theory"errorHandling";

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

val create_type_error_def = Define `
	create_type_error (locs, msg) = TypeError (concat [msg; implode " at "; locs_to_string locs])`;

val _ = export_theory()

