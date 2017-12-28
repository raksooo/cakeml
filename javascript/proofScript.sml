open preamble semanticsTheory javascriptSemanticsTheory javascriptBackendTheory primSemEnvTheory;

val _ = new_theory"proof"

val cakeml_semantics_def = Define `
  cakeml_semantics ffi prog = semantics_init ffi [] prog
`;

(*
`!(ffi:'ffi ffi_state) prog js. compile prog = SOME js
  ==> cakeml_semantics prog = javascript_semantics js`;
*)

(*
val compiler_proof = Q.store_thm("compiler_proof",
  `!expr js_expr. ast_to_ast expr = SOME js_expr ==> cml_sem expr = js_sem js_expr`,
  recInduct ast_to_ast_ind
  >> rpt strip_tac
  >> fs [cml_sem_def, js_sem_def, ast_to_ast_def]
  >> every_case_tac
  >> fs [cml_sem_def, js_sem_def, ast_to_ast_def]
  >> rveq
  >> fs [cml_sem_def, js_sem_def, ast_to_ast_def]
  >> metis_tac []
);
*)

val _ = export_theory()
