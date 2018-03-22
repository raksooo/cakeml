(*
open preamble jsAstTheory ffiTheory listTheory alistTheory;

val _ = new_theory"jsSemantics";

val _ = Datatype `
  js_scope = <| eid : num; lexEnv : (js_varN, js_v) alist |>;

  js_env = <| scopes : js_scope list |>;

	js_v = JSUndefined
       | JSLitv js_lit`;

val js_state_def = Datatype `
  js_state =
    <| clock : num
     ; scope_counter : num |>`;

val js_state_component_equality = fetch "-" "js_state_component_equality";

val initial_state_def = Define `
  initial_state = <| clock := 0; scope_counter := 0 |>`;

val js_fix_clock_def = Define `
	js_fix_clock st (st', env, res) =
		let cl = if st'.clock <= st.clock then st'.clock else st.clock
		in ((st' with <| clock := cl |>), env, res)`;

val js_dec_clock_def = Define `js_dec_clock st = st with <| clock := st.clock - 1 |>`;

val inc_scope_counter_def = Define `
  inc_scope_counter st = st with <| scope_counter := st.scope_counter + 1 |>`;

val base_scope_def = Define `
	base_scope = <| eid := 0; lexEnv := [] |>`;

val base_env_def = Define `base_env = <| scopes := [base_scope] |>`;

val enter_scope_def = Define `
	enter_scope st env = let
    st' = inc_scope_counter st;
    env' = env with <| scopes := (<| eid := st'.scope_counter; lexEnv := [] |> :: env.scopes) |>
  in (st', env')`;

val leave_scope_def = Define `
	leave_scope env = env with <| scopes := (TL env.scopes) |>`;

val scopeBind_def = Define `
	scopeBind scope var = scope with <| lexEnv := var :: scope.lexEnv |>`;

val scopeArgDeclare_def = Define `
  scopeArgDeclare scope (name, v) = case INDEX_FIND 0 ($= name o FST) scope.lexEnv of
    | SOME (i, _) => scope with <| lexEnv := LUPDATE (name, v) i scope.lexEnv |>
    | NONE => scopeBind scope (name, v)`;

val scopeLetDeclare_def = Define `
	scopeLetDeclare scope (name, v) =
		OPTION_MAP (\_. scopeBind scope (name, v)) (ALOOKUP scope.lexEnv name)`;

val scopesArgDeclare_def = Define `
	(scopesArgDeclare [] _ = NONE) /\
	(scopesArgDeclare (scope::scopes) var = SOME (scopeArgDeclare scope var :: scopes))`;

val scopesLetDeclare_def = Define `
	(scopesLetDeclare [] _ = NONE) /\
	(scopesLetDeclare (scope::scopes) var = OPTION_MAP (\s. s :: scopes) (scopeLetDeclare scope var))`;

val envArgDeclare_def = Define `
	envArgDeclare env var =
		OPTION_MAP (\s. env with <| scopes := s |>) (scopesArgDeclare env.scopes var)`;

val envLetDeclare_def = Define `
	envLetDeclare env var =
		OPTION_MAP (\s. env with <| scopes := s |>) (scopesLetDeclare env.scopes var)`;

val scopeLookup_def = Define `
	scopeLookup scope name = ALOOKUP scope.lexEnv name`;

val scopesLookup_def = Define `
	(scopesLookup [] _ = NONE) /\
	(scopesLookup (scope::scopes) name =
		OPTION_CHOICE (scopeLookup scope name) (scopesLookup scopes name))`;

val envLookup_def = Define `
	envLookup env name = scopesLookup env.scopes name`;

val merge_scopes_def = Define `
  (merge_scopes [] ss2 = []) /\
  (merge_scopes ss1 [] = ss1) /\
  (merge_scopes (s1::ss1) (s2::ss2) = if s1.eid = s2.eid
    then s1 :: (merge_scopes ss1 ss2)
    else ss2)`;

val merge_envs_def = Define `
  merge_envs env1 env2 = let scopes1 = REVERSE env1.scopes; scopes2 =  REVERSE env2.scopes in
    env1 with <| scopes := REVERSE (merge_scopes scopes1 scopes2) |>`;

val js_v_to_string_def = Define `
	js_v_to_string v = case v of
		| JSUndefined => "undefined"
    | JSLitv (JSBigInt n) => toString n
    | JSLitv (JSString str) => str
		| JSLitv (JSBool T) => "true"
		| JSLitv (JSBool F) => "false"
		| JSLitv JSNull => "null"`;

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

val is_truthy_def = Define `
	is_truthy v =
		~ (v = JSUndefined
		\/ v = JSLitv JSNull
		\/ v = JSLitv (JSBool F)
		\/ v = JSLitv (JSBigInt 0)
		\/ v = JSLitv (JSString ""))`;

val js_evaluate_bop_def = Define `
	(js_evaluate_bop JSPlus (JSLitv (JSString s)) v2 =
		JSRval [JSLitv (JSString (s ++ js_v_to_string v2))]) /\
	(js_evaluate_bop JSPlus v1 (JSLitv (JSString s)) =
		JSRval [JSLitv (JSString (js_v_to_string v1 ++ s))]) /\
	(js_evaluate_bop _ _ _ = NOT_IMPLEMENTED)`;

val js_evaluate_bop_ind = fetch "-" "js_evaluate_bop_ind";

val js_fix_clock_IMP = Q.prove(
	`js_fix_clock s x = (s1, env, res) ==> s1.clock <= s.clock`,
		Cases_on `x`
		>> rename1 `js_fix_clock _ (x, y)`
		>> Cases_on `y`
		>> fs [js_fix_clock_def]
		>> rw []
		>> fs []);

val js_exp_size_rel = Q.prove( `!args. SUM (MAP js_exp_size args) < js_exp1_size args + 1`,
	Induct >> fs [js_exp_size_def]);

val js_exp_size_not_zero = Q.prove(`!exp. 0 < js_exp_size exp`, Cases >> rw [js_exp_size_def]);

val js_evaluate_exp_def = tDefine "js_evaluate_exp" `
	(js_evaluate_exp st env [] = (st, env, JSRval [])) /\

  (js_evaluate_exp st env (e1::e2::es) = case js_fix_clock st (js_evaluate_exp st env [e1]) of
			| (st', env', JSRval v1) => (case js_evaluate_exp st' env' (e2::es) of
					|	(st2, env2, JSRval vs) => (st2, env2, JSRval (HD v1::vs))
					| res => res)
			| res => res) /\

	(js_evaluate_exp st env [JSLit lit] = (st, env, JSRval [JSLitv lit])) /\

	(js_evaluate_exp st env [JSVar name] = case envLookup env name of
			| SOME jsvar => (st, env, JSRval [jsvar])
			| NONE => (st, env, JSRerr ("ReferenceError: " ++ name ++ " is not defined"))) /\

	(js_evaluate_exp st env [JSBop JSAnd exp1 exp2] =
			case js_fix_clock st (js_evaluate_exp st env [exp1]) of
				| (st', env', JSRval [v1]) => if is_truthy v1
							then js_evaluate_exp st' env' [exp2]
							else (st', env', JSRval [v1])
				| res => res) /\

	(js_evaluate_exp st env [JSBop JSOr exp1 exp2] =
			case js_fix_clock st (js_evaluate_exp st env [exp1]) of
				| (st', env', JSRval [v1]) => if is_truthy v1
							then (st', env', JSRval [v1])
							else js_evaluate_exp st' env' [exp2]
				| res => res) /\

	(js_evaluate_exp st env [JSBop op exp1 exp2] =
		case js_fix_clock st (js_evaluate_exp st env [exp1]) of
			| (st', env', JSRval [v1]) => (case js_evaluate_exp st' env' [exp2] of
					| (st'', env'', JSRval [v2]) => (st'', env'', js_evaluate_bop op v1 v2)
					| res => res)
			| res => res) /\

	(js_evaluate_exp st env _ = (st, env, NOT_IMPLEMENTED))`
	(wf_rel_tac`inv_image ($< LEX $<) (λ(st, _, exps). (st.clock, (SUM o MAP js_exp_size) exps))`
		>> rw[js_exp_size_def, js_dec_clock_def,LESS_OR_EQ]
		>> imp_res_tac js_fix_clock_IMP
		>> simp[MAP_REVERSE,SUM_REVERSE, js_exp_size_not_zero]
		>> qspec_then `args` assume_tac js_exp_size_rel
		>> qspec_then `e2` assume_tac js_exp_size_not_zero
		>> fs []);

val js_evaluate_exp_ind = fetch "-" "js_evaluate_exp_ind";

val js_evaluate_clock = Q.store_thm("js_evaluate_clock",
	`!s1 env e s2 env2 r. js_evaluate_exp s1 env e = (s2, env2, r) ==> s2.clock <= s1.clock`,
  ho_match_mp_tac	js_evaluate_exp_ind
		>> rpt strip_tac
		>> fs [js_evaluate_exp_def, js_evaluate_bop_def, js_dec_clock_def, js_fix_clock_def]
		>> every_case_tac
		>> rfs []
		>> fs []
		>> imp_res_tac js_fix_clock_IMP
		>> fs []);

val fix_clock_js_evaluate_exp = Q.store_thm("fix_clock_js_evaluate_exp",
	`js_fix_clock st (js_evaluate_exp st env e) = js_evaluate_exp st env e`,
	Cases_on `js_evaluate_exp st env e`
		>> rename1 `js_fix_clock _ (x, y)`
		>> Cases_on `y`
		>> fs [js_fix_clock_def]
		>> imp_res_tac js_evaluate_clock
		>> fs [MIN_DEF,js_state_component_equality]);

val evaluate_def = save_thm("js_evaluate_exp_def",
	REWRITE_RULE [fix_clock_js_evaluate_exp] js_evaluate_exp_def);

val evaluate_ind = save_thm("js_evaluate_exp_ind",
	REWRITE_RULE [fix_clock_js_evaluate_exp] js_evaluate_exp_ind);

val evaluate_bop_length_proof = Q.store_thm("evaluate_bop_length_proof",
	`!op v1 v2 r. js_evaluate_bop op v1 v2 = JSRval r ==> LENGTH r = 1`,
	recInduct js_evaluate_bop_ind
		>> rpt strip_tac
		>> Cases_on `r`
		>> fs [js_evaluate_bop_def]);

val evaluate_length_proof = Q.store_thm("evaluate_length_proof",
  `!js_st js_env js_exps js_vs js_st' js_env'. js_evaluate_exp js_st js_env js_exps = (js_st', js_env', JSRval js_vs) ==> LENGTH js_exps = LENGTH js_vs`,
	recInduct js_evaluate_exp_ind
		>> rpt strip_tac
		>> fs [js_evaluate_exp_def, envLookup_def, scopesLookup_def]
		>> every_case_tac
		>> fs [fix_clock_js_evaluate_exp, js_evaluate_bop_def]
		>> rveq
		>> fs []
		>> imp_res_tac evaluate_bop_length_proof
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
			| (st', env', JSRval [v]) => (case envLetDeclare env' (name, v) of
					| SOME env2 => (st', env2, JSRval [JSUndefined])
					| NONE => (st', env',
							JSRerr ("SyntaxError: Identifier '" ++ name ++ "' has already been declared")))
			| res => res) /\
	(js_evaluate_stm st env _ = (st, env, NOT_IMPLEMENTED))`;

val js_evaluate_prog_def = Define `
  js_evaluate_prog st env prog = js_evaluate_stm st env prog`;

val _ = export_theory();
*)

