open preamble jsAstTheory ffiTheory listTheory alistTheory;

val _ = new_theory"jsSemantics";

val sequenceOption_def = Define `
  sequenceOption l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val _ = Datatype `
  js_scope = <| eid : num; function : bool; lexEnv : (js_varN, (js_v # bool)) alist |>;

  js_env = <| scopes : js_scope list |>;

	js_v =
    | JSUndefined
    | JSLitv js_lit
    | JSArrayv (js_v list)
    | JSObjectv ((js_varN, js_v) alist)
    | JSClosure (js_varN option) js_env (js_bind_element list) (js_stm list)`;

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
	base_scope = <| eid := 0; function := T; lexEnv := [] |>`;

val base_env_def = Define `base_env = <| scopes := [base_scope] |>`;

val enter_scope_def = Define `
	enter_scope st env f = let
    st' = inc_scope_counter st;
    env' = env with <| scopes := (<| eid := st'.scope_counter; function := f; lexEnv := [] |> :: env.scopes) |>
  in (st', env')`;

val leave_scope_def = Define `
	leave_scope env = env with <| scopes := (TL env.scopes) |>`;

val scopeBind_def = Define `
	scopeBind scope var = scope with <| lexEnv := var :: scope.lexEnv |>`;

val scopeVarDeclare_def = Define `
  scopeVarDeclare scope (name, v) = case INDEX_FIND 0 ($= name o FST) scope.lexEnv of
    | SOME (i, (_, (_, w))) => if ¬ w then NONE
        else SOME (scope with <| lexEnv := LUPDATE (name, v) i scope.lexEnv |>)
    | NONE => SOME (scopeBind scope (name, v))`;

val scopeLetDeclare_def = Define `
	scopeLetDeclare scope (name, v) = case ALOOKUP scope.lexEnv name of
    | SOME _ => NONE
    | NONE => SOME (scopeBind scope (name, v))`;

val scopesVarDeclare_def = Define `
	(scopesVarDeclare [] _ = NONE) /\
	(scopesVarDeclare (scope::scopes) var = if scope.function then
			OPTION_MAP (\s. s :: scopes) (scopeVarDeclare scope var)
		else
			OPTION_MAP (\ss. scope :: ss) (scopesVarDeclare scopes var))`;

val scopesLetDeclare_def = Define `
	(scopesLetDeclare [] _ = NONE) /\
	(scopesLetDeclare (scope::scopes) var = OPTION_MAP (\s. s :: scopes) (scopeLetDeclare scope var))`;

val envVarDeclare_def = Define `
	envVarDeclare env (name, v) =
		OPTION_MAP (\s. env with <| scopes := s |>) (scopesVarDeclare env.scopes (name, (v, T)))`;

val envLetDeclare_def = Define `
	envLetDeclare env (name, v) =
		OPTION_MAP (\s. env with <| scopes := s |>) (scopesLetDeclare env.scopes (name, (v, T)))`;

val envConstDeclare_def = Define `
	envConstDeclare env (name, v) =
		OPTION_MAP (\s. env with <| scopes := s |>) (scopesLetDeclare env.scopes (name, (v, F)))`;

val scopeLookup_def = Define `
	scopeLookup scope name = ALOOKUP scope.lexEnv name`;

val scopesLookup_def = Define `
	(scopesLookup [] _ = NONE) /\
	(scopesLookup (scope::scopes) name =
		OPTION_CHOICE (scopeLookup scope name) (scopesLookup scopes name))`;

val envLookup_def = Define `
	envLookup env name = OPTION_MAP FST (scopesLookup env.scopes name)`;

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
	(js_evaluate_bop JSPlusInt (JSLitv (JSBigInt a)) (JSLitv (JSBigInt b)) =
		JSRval [JSLitv (JSBigInt (a + b))]) /\
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

(*
val js_exp_size_rel = Q.prove( `!args. SUM (MAP js_exp_size args) < js_exp1_size args + 1`,
	Induct >> fs [js_exp_size_def]);
*)

val js_evaluate_bind_def = tDefine "js_evaluate_bind_def" `
	(js_evaluate_bind (JSBVar name) v = SOME [(name, v)]) /\
	(js_evaluate_bind (JSBArray [JSBRest b]) (JSArrayv vs) = js_evaluate_bind b (JSArrayv vs)) /\
	(js_evaluate_bind (JSBArray []) (JSArrayv _) = SOME []) /\
	(js_evaluate_bind (JSBArray (b::bs)) (JSArrayv []) = OPTION_MAP2 $++
		(js_evaluate_bind b JSUndefined) (js_evaluate_bind (JSBArray bs) (JSArrayv []))) /\
	(js_evaluate_bind (JSBArray (b::bs)) (JSArrayv (v::vs)) = OPTION_MAP2 $++
		(js_evaluate_bind b v) (js_evaluate_bind (JSBArray bs) (JSArrayv vs))) /\
	(js_evaluate_bind (JSBObject []) (JSObjectv _) = SOME []) /\
	(js_evaluate_bind (JSBObject ((bn, bv)::bs)) (JSObjectv vs) = let
			rest = js_evaluate_bind (JSBObject bs) (JSObjectv vs)
		in case ALOOKUP vs bn of
			| SOME vv => if IS_SOME bv then OPTION_MAP2 $++ (js_evaluate_bind (THE bv) vv) rest
							else OPTION_MAP (\r. (bn, vv) :: r) rest
			| NONE => if IS_SOME bv then OPTION_MAP2 $++ (js_evaluate_bind (THE bv) JSUndefined) rest
							else OPTION_MAP (\r. (bn, JSUndefined) :: r) rest) /\
	(js_evaluate_bind (JSBObject _) JSUndefined = NONE) /\
	(js_evaluate_bind (JSBObject _) (JSLitv JSNull) = NONE) /\
	(js_evaluate_bind _ _ = NONE)`
	cheat;

val declareMultiple_def = Define `
	(declareMultiple f env [] = SOME env) /\
	(declareMultiple f env (var::vars) = OPTION_BIND (f env var) (\env'. declareMultiple f env' vars))`;

val js_exp_size_not_zero = Q.prove(`!exp. 0 < js_exp_size exp`, Cases >> rw [js_exp_size_def]);

val isFunDecl_def = Define `
  isFunDecl _ = F`;

val isVarDecl_def = Define `
  (isVarDecl (JSVarDecl _ _) = T) /\
  (isVarDecl (JSLet _ _) = T) /\
  (isVarDecl (JSConst _ _) = T) /\
  (isVarDecl _ = F)`;

val evaluate_defns = Defn.Hol_multi_defns `
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

  (js_evaluate_exp st env [JSArray exps] = let 
        f = FOLDL (\a exp. case a of
          | (st', env', JSRerr err) => (st', env', JSRerr err)
          | (st', env', JSRval vs) => (case js_evaluate_exp st' env' [exp] of
              | (st2, env2, JSRval vs') => (case exp of
                | JSUop JSSpread exp' => (case vs' of
                  | [JSArrayv vs''] => (st2, env2, JSRval (vs ++ vs''))
                  | _ => (st2, env2, JSRerr "Not iterable"))
                | _ => (st2, env2, JSRval (vs ++ vs')))
              | res => res)) (st, env, JSRval []) exps
      in case f of
        | (st3, env3, JSRval vs3) => (st3, env3, JSRval [JSArrayv vs3])
        | res => res) /\

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

	(js_evaluate_exp st env [JSAFun pars exp] = let (st', env') = enter_scope st env T
		 in (st', env, JSRval [JSClosure NONE env' pars exp])) /\

	(js_evaluate_exp st env [JSFun name pars exp] = let (st', env') = enter_scope st env T
		 in (st', env, JSRval [JSClosure (SOME name) env' pars exp])) /\

  (js_evaluate_exp st env [JSApp exp args] = case js_fix_clock st (js_evaluate_exp st env [exp]) of
    | (st', env', JSRval [JSClosure name cenv pars body]) =>
        (case js_fix_clock st' (js_evaluate_exp st' env' [JSArray args]) of
          | (st2, env2, JSRval [JSArrayv vs]) => let
								parargs = OPTION_MAP FLAT
									(sequenceOption (MAP (UNCURRY js_evaluate_bind) (js_par_zip (pars, vs))));
								withname =
									OPTION_BIND name (\n. envVarDeclare cenv (n, (JSClosure name cenv pars body)));
								cenv' = if IS_SOME withname then THE withname else cenv
							in (case parargs of
								| SOME parargs =>
										(case declareMultiple envVarDeclare (merge_envs cenv' env2) parargs of
											| SOME cenv2 => if st2.clock = 0 then (st2, env2, CLOCK_TIMEOUT)
													else let (st3, cenv3, res) = js_evaluate_stm (js_dec_clock st2) cenv2 body
														in (st3, leave_scope cenv3, res)
											| NONE => (st2, env2, JSRerr "Should not happen"))
								| NONE => (st2, env2, JSRerr "Invalid pattern"))
          | res => res)
			| (st', env', JSRval [JSLitv lit]) => (st', env',
          JSRerr ("TypeError: " ++ (js_v_to_string (JSLitv lit)) ++ " is not a function"))
      | (st', env', JSRval [JSUndefined]) => (st', env',
          JSRerr "TypeError: undefined is not a function")
      | res => res) /\

	(js_evaluate_exp st env _ = (st, env, NOT_IMPLEMENTED)) /\

	(js_evaluate_stm2 st env [] = (st, env, JSRval [])) /\
	(js_evaluate_stm2 st env ((JSReturn exp)::ss) = js_evaluate_exp st env [exp]) /\
	(js_evaluate_stm2 st env (s1::s2::ss) = case js_evaluate_stm2 st env [s1] of
			| (st', env', JSRval v1) => (case js_evaluate_stm2 st' env' (s2::ss) of
					| (st2, env2, JSRval vs) => (st2, env2, JSRval (HD v1::vs))
					| res => res)
			| res => res) /\
	(js_evaluate_stm2 st env [JSExp exp] = js_evaluate_exp st env [exp]) /\
	(js_evaluate_stm2 st env [JSVarDecl be exp] = case js_evaluate_exp st env [exp] of
			| (st', env', JSRval [v]) => 
				(case OPTION_BIND (js_evaluate_bind be v) (declareMultiple envVarDeclare env') of
					| SOME env2 => (st', env2, JSRval [JSUndefined])
					| NONE => (st', env', JSRerr "Invalid pattern"))
			| res => res) /\
	(js_evaluate_stm2 st env [JSLet be exp] = case js_evaluate_exp st env [exp] of
			| (st', env', JSRval [v]) => (case js_evaluate_bind be v of
				| SOME vs => (case declareMultiple envLetDeclare env' vs of
					| SOME env2 => (st', env2, JSRval [JSUndefined])
					| NONE => (st', env',
							JSRerr "SyntaxError: Identifier has already been declared"))
				| NONE => (st', env', JSRerr "Invalid pattern"))
			| res => res) /\
	(js_evaluate_stm2 st env [JSConst be exp] = case js_evaluate_exp st env [exp] of
			| (st', env', JSRval [v]) => (case js_evaluate_bind be v of
				| SOME vs => (case declareMultiple envLetDeclare env' vs of
					| SOME env2 => (st', env2, JSRval [JSUndefined])
					| NONE => (st', env',
							JSRerr ("SyntaxError: Identifier has already been declared")))
				| NONE => (st', env', JSRerr "Invalid pattern"))
			| res => res) /\
	(js_evaluate_stm2 st env _ = (st, env, NOT_IMPLEMENTED)) /\

  (js_evaluate_stm st env stms = let
      funs = FILTER isFunDecl stms;
      vars = FILTER isVarDecl stms;
      others = FILTER (\stm. ~ (isFunDecl stm \/ isVarDecl stm)) stms
    in js_evaluate_stm2 st env (funs ++ vars ++ others))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) evaluate_defns;
val js_evaluate_exp_def = fetch "-" "js_evaluate_exp_def";

val js_evaluate_exp_ind = fetch "-" "js_evaluate_exp_ind";

(*
	(wf_rel_tac`inv_image ($< LEX $<) (λ(st, _, exps). (st.clock, (SUM o MAP js_exp_size) exps))`
		>> rw[js_exp_size_def, js_dec_clock_def,LESS_OR_EQ]
		>> imp_res_tac js_fix_clock_IMP
		>> simp[MAP_REVERSE,SUM_REVERSE, js_exp_size_not_zero]
		>> qspec_then `args` assume_tac js_exp_size_rel
		>> qspec_then `e2` assume_tac js_exp_size_not_zero
		>> fs []);
*)

(*
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
*)

val evaluate_bop_length_proof = Q.store_thm("evaluate_bop_length_proof",
	`!op v1 v2 r. js_evaluate_bop op v1 v2 = JSRval r ==> LENGTH r = 1`,
	recInduct js_evaluate_bop_ind
		>> rpt strip_tac
		>> Cases_on `r`
		>> fs [js_evaluate_bop_def]);

(*
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
*)

val js_evaluate_prog_def = Define `
  js_evaluate_prog st env prog = js_evaluate_stm st env prog`;

val _ = export_theory();

