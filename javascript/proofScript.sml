(*
open preamble compilerTheory evaluateTheory javascriptSemanticsTheory;
open preamble compilerTheory semanticsTheory javascriptSemanticsTheory;

val _ = new_theory "proof"

val empty_cml_state_def = Define `
	empty_cml_state = <| clock := 0; refs := []; ffi := initial_ffi_state 0 0; next_type_stamp := 0; next_exn_stamp := 0 |>`;

val empty_cml_sem_env_def = Define `
	empty_cml_sem_env = <| v := nsEmpty; c := nsEmpty |>`;

``'ffi`` |> type_of;
``initial_ffi_state`` |> type_of;
``evaluate_decs empty_cml_state empty_cml_sem_env`` |> type_of;
``evaluate_prog`` |> type_of;

val trd_def = Define `
	trd (_, _, c) = c`;

(*
`!prog js_prog st clock env. (compile prog = SOME js_prog)
  ==> (SND (evaluate_prog (st with <| clock := clock |>) env prog)
		= trd (js_evaluate_prog <| clock := clock |> base_env js_prog))`;
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
*)
