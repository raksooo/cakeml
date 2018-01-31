open preamble javascriptAstTheory ffiTheory listTheory;

val _ = new_theory"javascriptSemantics";

val js_v_def = Datatype `
	js_v =
		| JSUndefined
		| JSLitv js_lit
		| JSFunv (js_varN list) js_exp`;

val state_def = Datatype `state = <| clock : num |>`;

val fix_clock_def = Define `
	fix_clock st (st', env, res) =
		let cl = if st'.clock <= st.clock then st'.clock else st.clock
		in ((st' with <| clock := cl |>), env, res)`;

val dec_clock_def = Define `dec_clock st = st with <| clock := st.clock - 1 |>`;

val js_var_def = Datatype `
	js_var =
		<| value : js_v
		 ; writable : bool |>`;

val js_context_def = type_abbrev("js_context", ``:(js_varN # js_var) list``);

val js_env_def = Datatype `js_env = <| cl : js_context list |>`;

val base_context_def = Define `
	base_context = [[("undefined", <| value := JSUndefined; writable := F |>)]]`;

val base_env_def = Define `base_env = <| cl := base_context |>`;

val enter_context_def = Define `
	enter_context env = env with <| cl := ([] :: env.cl) |>`;

val leave_context_def = Define `
	leave_context env = env with <| cl := (TL env.cl) |>`;

val cvar_update_def = Define `
	(cvar_update [] _ _ = NONE) /\
	(cvar_update (ctx::ctxs) name value = case INDEX_FIND 0 (\var. FST var = name) ctx of
		| SOME (i, _, old) => if old.writable
        then SOME ((LUPDATE (name, <| value := value; writable := T |>) i ctx) :: ctxs)
        else SOME (ctx :: ctxs)
		| NONE => case cvar_update ctxs name value of
				| SOME ctxs' => SOME (ctx :: ctxs')
				| NONE => NONE)`;

val cvar_assignment_def = Define `
	cvar_assignment ctxs name value = case cvar_update ctxs name value of
		| SOME ctxs' => ctxs'
		| NONE => let rev = REVERSE ctxs in
				REVERSE (((name, <| value := value; writable := T |>) :: (HD ctxs)) :: (TL ctxs))`;

val var_assignment_def = Define `
	var_assignent env name value = env with <| cl := cvar_assignment env.cl name value |>`;

val var_declaration_def = Define `
	(var_declaration env [] = SOME env) /\
	(var_declaration env ((name, value)::vs) =
		case INDEX_FIND 0 (\var. FST var = name) (HD env.cl) of
			| SOME _ => NONE
			| NONE => let
					ctx' = (name, <| value := value; writable := T |>) :: (HD env.cl);
					env' = env with <| cl := (ctx' :: (TL env.cl)) |>
					in var_declaration env' vs)`;

val lookup_cvar_def = Define `
	(lookup_cvar [] _ = NONE) /\
	(lookup_cvar (ctx::ctxs) name = case FIND (\var. FST var = name) ctx of
		| (SOME (_, value)) => SOME value.value
		| NONE => lookup_cvar ctxs name)`;

val lookup_var_def = Define `
	lookup_var env name = lookup_cvar env.cl name`;

val js_v_to_string_def = Define `
	js_v_to_string v = case v of
		| JSUndefined => "undefined"
    | JSLitv (JSInteger n) => toString n
    | JSLitv (JSString str) => str
		| JSLitv (JSBool T) => "true"
		| JSLitv (JSBool F) => "false"
		| JSLitv JSNull => "null"
		| JSFunv _ _ => "function"`;

val js_result_def = Datatype `
 js_result =
  | JSRval (js_v list)
	| JSRerr string
	| CLOCK_TIMEOUT
	| NOT_IMPLEMENTED`;

val js_par_zip_def = Define `
	(js_par_zip ([], args) = []) /\
	(js_par_zip (par::pars, []) = (par, JSUndefined) :: (js_par_zip (pars, []))) /\
	(js_par_zip (par::pars, arg::args) = (par, arg) :: (js_par_zip (pars, args)))`;

val js_to_boolean = Define `
	js_to_boolean v =
		~ (v = JSUndefined
		\/ v = JSLitv JSNull
		\/ v = JSLitv (JSBool F)
		\/ v = JSLitv (JSInteger 0)
		\/ v = JSLitv (JSString ""))`;

val js_evaluate_bop_def = Define `
	(js_evaluate_bop JSAnd v1 v2 = if js_to_boolean v1 then v2 else v1) /\
	(js_evaluate_bop JSOr v1 v2 = if js_to_boolean v1 then v1 else v2) /\
	(js_evaluate_bop JSPlus (JSLitv (JSString s)) v2 = JSLitv (JSString (s ++ js_v_to_string v2))) /\
	(js_evaluate_bop JSPlus v1 (JSLitv (JSString s)) = JSLitv (JSString (js_v_to_string v1 ++ s)))`;

val fix_clock_IMP = Q.prove(
	`fix_clock s x = (s1, res) ==> s1.clock <= s.clock`,
		Cases_on `x`
		>> rename1 `fix_clock _ (x, y)`
		>> Cases_on `y`
		>> fs [fix_clock_def]
		>> rw []
		>> fs []);

val js_exp_size_rel = Q.prove( `!args. SUM (MAP js_exp_size args) < js_exp1_size args + 1`,
	Induct >> fs [js_exp_size_def]);

val js_exp_size_not_zero = Q.prove(`!exp. 0 < js_exp_size exp`, Cases >> rw [js_exp_size_def]);

val js_evaluate_exp_def = tDefine "js_evaluate_exp" `
	(js_evaluate_exp st env [] = (st, env, JSRval [])) /\
  (js_evaluate_exp st env (e1::e2::es) = case fix_clock st (js_evaluate_exp st env [e1]) of
			| (st', env', JSRval v1) => (case js_evaluate_exp st' env' (e2::es) of
					|	(st2, env2, JSRval vs) => (st2, env2, JSRval (HD v1::vs))
					| res => res)
			| res => res) /\
	(js_evaluate_exp st env [JSLit lit] = (st, env, JSRval [JSLitv lit])) /\
	(js_evaluate_exp st env [JSAFun pars exp] = (st, env, JSRval [JSFunv pars exp])) /\
	(js_evaluate_exp st env [JSVar name] = case lookup_var env name of
			| SOME jsvar => (st, env, JSRval [jsvar])
			| NONE => (st, env, JSRerr ("ReferenceError: " ++ name ++ " is not defined"))) /\
	(js_evaluate_exp st env [JSApp exp args] = case fix_clock st (js_evaluate_exp st env [exp]) of
			| (st', env', JSRval [JSLitv lit]) => (st', env',
					JSRerr ("TypeError: " ++ (js_v_to_string (JSLitv lit)) ++ " is not a function"))
			| (st', env', JSRval [JSUndefined]) => (st', env',
					JSRerr "TypeError: undefined is not a function")
			| (st', env', JSRval [JSFunv pars body]) => (case fix_clock st' (js_evaluate_exp st' env' args) of
					| (st2, env2, JSRval vs) => let
								env3 = enter_context env2;
								parargs = js_par_zip (pars, vs)
							in (case var_declaration env3 parargs of
								| SOME env4 => if st2.clock = 0 then
											(st2, env4, CLOCK_TIMEOUT)
										else
											let (st3, _, res) = js_evaluate_exp (dec_clock st2) env4 [body]
											in (st3, env2, res)
								| NONE => (st', env',
										JSRerr "SyntaxError: Duplicate parameter name not allowed in this context"))
					| res => res)
			| res => res) /\
	(js_evaluate_exp st env [JSBop op exp1 exp2] = case js_evaluate_exp st env [exp1; exp2] of
			| (st', env', JSRval [v1; v2]) => (st', env', JSRval [js_evaluate_bop op v1 v2])
			| res => res) /\
	(js_evaluate_exp st env _ = (st, env, NOT_IMPLEMENTED))`
	(wf_rel_tac`inv_image ($< LEX $<) (λ(st, _, exps). (st.clock, (SUM o MAP js_exp_size) exps))`
		>> rw[js_exp_size_def, dec_clock_def,LESS_OR_EQ]
		>> imp_res_tac fix_clock_IMP
		>> simp[MAP_REVERSE,SUM_REVERSE, js_exp_size_not_zero]
		>> qspec_then `args` assume_tac js_exp_size_rel
		>> qspec_then `e2` assume_tac js_exp_size_not_zero
		>> fs []);

val js_evaluate_stm_def = Define `
	(js_evaluate_stm st env [] = (st, env, JSRval [])) /\
	(js_evaluate_stm st env (s1::s2::ss) = case js_evaluate_stm st env [s1] of
			| (st', env', JSRval v1) => (case js_evaluate_stm st' env' (s2::ss) of
					| (st2, env2, JSRval vs) => (st2, env2, JSRval (HD v1::vs))
					| res => res)
			| res => res) /\
	(js_evaluate_stm st env [JSExp exp] = js_evaluate_exp st env [exp]) /\
	(js_evaluate_stm st env [JSLet name exp] = case js_evaluate_exp st env [exp] of
			| (st', env', JSRval [v]) => (case var_declaration env' [(name, v)] of
					| SOME env2 => (st', env2, JSRval [JSUndefined])
					| NONE => (st', env',
							JSRerr ("SyntaxError: Identifier '" ++ name ++ "' has already been declared")))
			| res => res) /\
	(js_evaluate_stm st env _ = (st, env, NOT_IMPLEMENTED))`;

val js_evaluate_prog_def = Define `
	(js_evaluate_prog st env [] = (st, env, JSRval [])) /\
	(js_evaluate_prog st env (t1::t2::ts) = case js_evaluate_prog st env [t1] of
			| (st', env', JSRval v1) => (case js_evaluate_prog st' env' (t2::ts) of
					| (st2, env2, JSRval vs) => (st2, env2, JSRval (HD v1::vs))
					| res => res)
			| res => res) /\
	(js_evaluate_prog st env [JSStm stm] = js_evaluate_stm st env [stm])`;

val _ = export_theory();

