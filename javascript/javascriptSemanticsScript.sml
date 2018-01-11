open preamble javascriptAstTheory ffiTheory listTheory;

val _ = new_theory"javascriptSemantics";

val js_v_def = Hol_datatype `
	js_v =
		| JSUndefined
		| JSLitv of js_lit
		| JSFunv of js_varN list => js_exp`;

val state_def = Hol_datatype `
	state =
		<| clock : num
		 (*; refs : v store*)
		 ; defined_mods : (string list) set
		 |>`;

val fix_clock_def = Define `
	fix_clock st (st', res) =
		let cl = if st'.clock <= st.clock then st'.clock else st.clock
		in ((st' with <| clock := cl |>), res)`;

val dec_clock_def = Define `
 dec_clock st = st with <| clock := st.clock - 1 |>`;

val js_result_def = Hol_datatype `
 js_result =
  | JSRval of 'a
  | JSRerr of 'b`;

val js_evaluate_exp_def = Define `
	(js_evaluate_exp st env [] = (st, JSRval [])) /\
  (js_evaluate_exp st env (e1::e2::es) =
		case fix_clock st (js_evaluate_exp st env [e1]) of
				(st', JSRval v1) =>
					(case js_evaluate_exp st' env (e2::es) of
							(st'', JSRval vs) => (st'', JSRval (HD v1::vs))
						| res => res)
			| res => res) /\
	(js_evaluate_exp st env [JSLit (JSBool b)] = (st, JSRval [JSLitv (JSBool b)]))`;

val _ = export_theory();

