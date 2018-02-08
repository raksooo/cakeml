open preamble compilerTheory javascriptSemanticsTheory javascriptBackendTheory
		 semanticPrimitivesTheory evaluateTheory stringTheory;

val _ = new_theory "proof"

(*
val empty_cml_state_def = Define `
	empty_cml_state ffi = <| clock := 0; refs := []; ffi := ffi; next_type_stamp := 0; next_exn_stamp := 0 |>`;
*)

val empty_cml_sem_env_def = Define `
	empty_cml_sem_env = <| v := nsEmpty; c := nsEmpty |>`;

val trd_def = Define `
	trd (_, _, c) = c`;

val all = Define `
	all f l = NULL (FILTER ($~ o f) l)`;

val v_rel_def = Hol_reln `
	(!i. v_rel (Litv (IntLit i)) (JSLitv (JSInteger i))) /\

	(!s. v_rel (Litv (StrLit s)) (JSLitv (JSString s))) /\

	(v_rel (Conv (SOME (TypeStamp "true" bool_type_num)) []) (JSLitv (JSBool T))) /\
	(v_rel (Conv (SOME (TypeStamp "false" bool_type_num)) []) (JSLitv (JSBool F)))`;

`!exps js_exps st clock.
	ata_exp exps = SOME js_exps /\
	trd (js_evaluate_exp (st with <| clock := clock |>) base_env js_exps) = JSRval vs
		==> trd (js_evaluate_exp (st with <| clock := clock + 1 |>) base_env js_exps) = JSRval vs`;

`!exps js_exps vs js_vs st.
	(ata_exp exps = SOME js_exps /\
	SND (evaluate st empty_cml_sem_env exps) = Rval vs)
		==> ?js_st. trd (js_evaluate_exp js_st base_env js_exps) = JSRval js_vs /\
      all (UNCURRY v_rel) (ZIP (vs, js_vs))`;

recInduct ata_exp_ind
rpt strip_tac
fs [js_evaluate_exp_def]

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

