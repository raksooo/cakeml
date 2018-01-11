open preamble javascriptAstTheory ffiTheory listTheory;

val _ = new_theory"javascriptSemantics";

val js_v_def = Hol_datatype `
	js_v =
		| JSUndefined
		| JSLitv of js_lit
		| JSFunv of js_varN list => js_exp`;

val state_def = Hol_datatype `state = <| clock : num |>`;

val fix_clock_def = Define `
	fix_clock st (st', env, res) =
		let cl = if st'.clock <= st.clock then st'.clock else st.clock
		in ((st' with <| clock := cl |>), env, res)`;

val dec_clock_def = Define `dec_clock st = st with <| clock := st.clock - 1 |>`;

val js_var_def = Hol_datatype `
	js_var =
		<| value : js_v
		 ; writable : bool |>`;

val js_context_def = type_abbrev("js_context", ``:(js_varN # js_var) list``);

val js_env_def = Hol_datatype `js_env = <| cl : js_context list |>`;

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
	(var_declaration env ((name, value)::vs) = let
			ctxs = env.cl
		in case INDEX_FIND 0 (\var. FST var = name) (HD ctxs) of
			| SOME _ => NONE
			| NONE => let
					ctx' = (name, <| value := value; writable := T |>) :: (HD ctxs);
					env' = env with <| cl := (ctx' :: (TL ctxs)) |>
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
    | JSLitv (JSIntLit n) => toString n
    | JSLitv (JSStrLit str) => str
		| JSLitv (JSBool T) => "true"
		| JSLitv (JSBool F) => "false"
		| JSLitv JSNull => "null"
		| JSFunv _ _ => "function"`;

val js_result_def = Hol_datatype `
 js_result =
  | JSRval of 'a
	| JSRerr of 'b
	| NOT_IMPLEMENTED`;

val js_par_zip_def = Define `
	(js_par_zip ([], args) = []) /\
	(js_par_zip (par::pars, []) = (par, JSUndefined) :: (js_par_zip (pars, []))) /\
	(js_par_zip (par::pars, arg::args) = (par, arg) :: (js_par_zip (pars, args)))`;

val js_evaluate_exp_def = tDefine "js_evaluate_exp" `
	(js_evaluate_exp st env [] = (st, env, JSRval [])) /\
  (js_evaluate_exp st env (e1::e2::es) =
		case fix_clock st (js_evaluate_exp st env [e1]) of
				(st', env', JSRval v1) =>
					(case js_evaluate_exp st' env' (e2::es) of
							(st'', env'', JSRval vs) => (st'', env'', JSRval (HD v1::vs))
						| res => res)
			| res => res) /\
	(js_evaluate_exp st env [JSLit lit] = (st, env, JSRval [JSLitv lit])) /\
	(js_evaluate_exp st env [JSVar name] = case lookup_var env name of
		| SOME jsvar => (st, env, JSRval [jsvar])
		| NONE => (st, env, JSRerr ("ReferenceError: " ++ name ++ " is not defined"))) /\
	(js_evaluate_exp st env [JSApp (JSVar name) args] = case js_evaluate_exp st env [JSVar name] of
		| (st', env', JSRval [(JSFunv pars exp)]) => js_evaluate_exp st env [JSApp (JSFun pars exp) args]
		| res => res) /\
	(js_evaluate_exp st env [JSApp (JSFun pars exp) args] = case js_evaluate_exp st env args of
		| (st', env', JSRval vs) => (case var_declaration (enter_context env') (js_par_zip (pars, vs)) of
				| SOME env'' => js_evaluate_exp st' env'' [exp]
				| NONE => (st', env',
						JSRerr "SyntaxError: Duplicate parameter name not allowed in this context"))
		| res => res) /\
	(js_evaluate_exp st env _ = (st, env, NOT_IMPLEMENTED))`
	(cheat);

val _ = export_theory();

