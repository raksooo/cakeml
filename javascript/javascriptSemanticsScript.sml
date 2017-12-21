open preamble javascriptAstTheory semanticPrimitivesTheory;

val _ = new_theory"javascriptSemantics";

val fix_clock_def = Define `
	fix_clock s (s', res) =
		let cl = if s'.clock <= s.clock then s'.clock else s.clock
		in ((s' with <| clock := cl |>), res)`;

val js_evaluate_def = Define `
	(js_evaluate st env [] = (st, Rval [])) /\
  (js_evaluate st env (e1::e2::es) =
		case fix_clock st (js_evaluate st env [e1]) of
				(st', Rval v1) =>
					(case js_evaluate st' env (e2::es) of
							(st'', Rval vs) => (st'', Rval (HD v1::vs))
						| res => res)
			| res => res)`;

val _ = export_theory();

