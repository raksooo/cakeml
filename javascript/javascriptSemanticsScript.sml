open preamble javascriptAstTheory ffiTheory listTheory;

val _ = new_theory"javascriptSemantics";

val _ = Datatype `
	js_var = <| value : js_v; writable : bool |>;

  js_scope = <| eid : num; lexEnv : (js_varN # js_var) list |>;

  js_env = <| scopes : js_scope list |>;

	js_v = JSUndefined
       | JSLitv js_lit
       | JSClosure (js_varN option) js_env (js_varN list) js_exp`;

val state_def = Datatype `
  state =
    <| clock : num
     ; scope_counter : num |>`;

val initial_state_def = Define `
  initial_state = <| clock := 0; scope_counter := 0 |>`;

val fix_clock_def = Define `
	fix_clock st (st', env, res) =
		let cl = if st'.clock <= st.clock then st'.clock else st.clock
		in ((st' with <| clock := cl |>), env, res)`;

val dec_clock_def = Define `dec_clock st = st with <| clock := st.clock - 1 |>`;

val inc_scope_counter_def = Define `
  inc_scope_counter st = st with <| scope_counter := st.scope_counter + 1 |>`;

val base_scope_def = Define `
	base_scope = <| eid := 0; lexEnv := [("undefined", <| value := JSUndefined; writable := F |>)] |>`;

val base_env_def = Define `base_env = <| scopes := [base_scope] |>`;

val enter_scope_def = Define `
	enter_scope st env = let
    st' = inc_scope_counter st;
    env' = env with <| scopes := (<| eid := st'.scope_counter; lexEnv := [] |> :: env.scopes) |>
  in (st', env')`;

val leave_scope_def = Define `
	leave_scope env = env with <| scopes := (TL env.scopes) |>`;

val add_var_to_scope_def = Define `
  add_var_to_scope scope (name, var) = case INDEX_FIND 0 (\var. FST var = name) scope.lexEnv of
    | SOME (i, _, old) => if old = var then scope
        else scope with <| lexEnv := LUPDATE (name, var) i scope.lexEnv |>
    | NONE => scope with <| lexEnv := (name, var) :: scope.lexEnv |>`;

val add_to_top_scope_def = Define `
  add_to_top_scope env vars = let
      add = \scope (name, v). add_var_to_scope scope (name, <| value := v; writable := T |>);
      scope = FOLDL add (HD env.scopes) vars
    in env with <| scopes := scope :: (TL env.scopes) |>`;

val cvar_update_def = Define `
	(cvar_update [] _ _ = NONE) /\
	(cvar_update (scope::scopes) name value = case INDEX_FIND 0 (\var. FST var = name) scope.lexEnv of
		| SOME (i, _, old) => if old.writable
        then let
            lexEnv' = LUPDATE (name, <| value := value; writable := T |>) i scope.lexEnv
          in SOME ((scope with <| lexEnv := lexEnv' |>) :: scopes)
        else SOME (scope :: scopes)
		| NONE => case cvar_update scopes name value of
				| SOME scopes' => SOME (scope :: scopes')
				| NONE => NONE)`;

val cvar_assignment_def = Define `
	cvar_assignment (scope::scopes) name value = case cvar_update (scope::scopes) name value of
		| SOME scopes' => scopes'
		| NONE => let
          rev = REVERSE (scope::scopes);
          lexEnv' = (name, <| value := value; writable := T |>) :: scope.lexEnv
        in REVERSE ((scope with <| lexEnv := lexEnv' |>) :: scopes)`;

val var_assignment_def = Define `
	var_assignent env name value = env with <| scopes := cvar_assignment env.scopes name value |>`;

val var_declaration_def = Define `
	(var_declaration env [] = SOME env) /\
	(var_declaration env ((name, value)::vs) =
		case INDEX_FIND 0 (\var. FST var = name) ((HD env.scopes).lexEnv) of
			| SOME _ => NONE
			| NONE => let
					lexEnv' = (name, <| value := value; writable := T |>) :: (HD env.scopes).lexEnv;
          scope' = (HD env.scopes) with <| lexEnv := lexEnv' |>;
					env' = env with <| scopes := (scope' :: (TL env.scopes)) |>
        in var_declaration env' vs)`;

val lookup_cvar_def = Define `
	(lookup_cvar [] _ = NONE) /\
	(lookup_cvar (scope::scopes) name = case FIND (\var. FST var = name) scope.lexEnv of
		| (SOME (_, value)) => SOME value.value
		| NONE => lookup_cvar scopes name)`;

val lookup_var_def = Define `
	lookup_var env name = lookup_cvar env.scopes name`;

val merge_scope_def = Define `
  merge_scope s1 s2 = FOLDL (\s var. add_var_to_scope s var) s1 s2.lexEnv`;

val merge_scopes_def = Define `
  (merge_scopes [] ss2 = []) /\
  (merge_scopes ss1 [] = ss1) /\
  (merge_scopes (s1::ss1) (s2::ss2) = if s1.eid = s2.eid
    then (merge_scope s1 s2) :: (merge_scopes ss1 ss2)
    else (s1::ss1))`;

val merge_envs_def = Define `
  merge_envs env1 env2 = let scopes1 = REVERSE env1.scopes; scopes2 =  REVERSE env2.scopes in
    env1 with <| scopes := REVERSE (merge_scopes scopes1 scopes2) |>`;

val js_v_to_string_def = Define `
	js_v_to_string v = case v of
		| JSUndefined => "undefined"
    | JSLitv (JSInteger n) => toString n
    | JSLitv (JSString str) => str
		| JSLitv (JSBool T) => "true"
		| JSLitv (JSBool F) => "false"
		| JSLitv JSNull => "null"
		| JSClosure _ _ _ _ => "function"`;

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
		\/ v = JSLitv (JSInteger 0)
		\/ v = JSLitv (JSString ""))`;

val is_callable_def = Define `
  (is_callable (JSClosure _ _ _ _) = T) /\
  (is_callable _ = F)`;

val js_evaluate_bop_def = Define `
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

	(js_evaluate_exp st env [JSAFun pars exp] = let (st', env') = enter_scope st env
      in (st', env, JSRval [JSClosure NONE env' pars exp])) /\

	(js_evaluate_exp st env [JSFun name pars exp] = let (st', env') = enter_scope st env
      in (st', env, JSRval [JSClosure (SOME name) env' pars exp])) /\

	(js_evaluate_exp st env [JSVar name] = case lookup_var env name of
			| SOME jsvar => (st, env, JSRval [jsvar])
			| NONE => (st, env, JSRerr ("ReferenceError: " ++ name ++ " is not defined"))) /\

	(js_evaluate_exp st env [JSApp exp args] = case fix_clock st (js_evaluate_exp st env [exp]) of
			| (st', env', JSRval [JSClosure name cenv pars body]) =>
          (case fix_clock st' (js_evaluate_exp st' env' args) of
            | (st2, env2, JSRval vs) => let
                  parargs = js_par_zip (pars, vs);
                  cenv' = (case name of
                    | SOME name' => add_to_top_scope cenv [(name', (JSClosure name cenv pars body))]
                    | NONE => env2);
                  env3 = add_to_top_scope (merge_envs cenv' env2) parargs
                in if st2.clock = 0 then (st2, env2, CLOCK_TIMEOUT)
                  else
                    let (st3, env4, res) = js_evaluate_exp (dec_clock st2) env3 [body]
                    in (st3, leave_scope env4, res)
            | res => res)
			| (st', env', JSRval [JSLitv lit]) => (st', env',
					JSRerr ("TypeError: " ++ (js_v_to_string (JSLitv lit)) ++ " is not a function"))
			| (st', env', JSRval [JSUndefined]) => (st', env',
					JSRerr "TypeError: undefined is not a function")
			| res => res) /\

	(js_evaluate_exp st env [JSBop JSAnd exp1 exp2] =
			case fix_clock st (js_evaluate_exp st env [exp1]) of
				| (st', env', JSRval [v1]) => if is_truthy v1
							then js_evaluate_exp st' env' [exp2]
							else (st', env', JSRval [v1])
				| res => res) /\

	(js_evaluate_exp st env [JSBop JSOr exp1 exp2] =
			case fix_clock st (js_evaluate_exp st env [exp1]) of
				| (st', env', JSRval [v1]) => if is_truthy v1
							then (st', env', JSRval [v1])
							else js_evaluate_exp st' env' [exp2]
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
  js_evaluate_prog st env prog = js_evaluate_stm st env prog`;

val _ = export_theory();

