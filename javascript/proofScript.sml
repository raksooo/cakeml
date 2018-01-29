open preamble compilerTheory evaluateTheory javascriptSemanticsTheory;

val _ = new_theory "proof"

val js_v_to_cml_v_def = Define `
	(js_v_to_cml_v (JSLitv (JSInteger n)) = Litv (IntLit n)) /\
	(js_v_to_cml_v (JSLitv (JSString s)) = Litv (StrLit s))`;
	(*(js_v_to_cml_v (JSLitv (JSBool b)) = Litv (StrLit n))*)

val js_r_to_cml_r_def = Define `
	(js_r_to_cml_r (_, _, JSRerr err) = Rerr (Rraise (prim_exn "error"))) /\
	(js_r_to_cml_r (_, _, JSRval vals) = Rval (MAP js_v_to_cml_v vals))`;

``SND (evaluate_prog (st with <| clock := cl |>) env prog)`` |> type_of;
``js_r_to_cml_r (js_evaluate_prog <| clock := cl |> base_env js_prog)`` |> type_of;

(*
`!prog js_prog st cl env. (compile_to_javascript prog = Success js_prog)
  ==> (SND (evaluate_prog (st with <| clock := cl |>) env prog)
		= js_r_to_cml_r (js_evaluate_prog <| clock := cl |> base_env js_prog))`;
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
