(*
open preamble compilerTheory javascriptSemanticsTheory javascriptBackendTheory
		 semanticPrimitivesTheory evaluateTheory terminationTheory stringTheory;

val _ = new_theory "proof"

val optionSequence_def = Define `
  optionSequence l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val flattenScopes_def = Define `
  flattenScopes eid scopes = let
      scopes' = MAP (\scope. scope.lexEnv) scopes
    in <| eid := eid; lexEnv := FLAT scopes' |>`;

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
	(!i. v_rel (Litv (IntLit i)) (JSLitv (JSInteger i))) /\
	(!s. v_rel (Litv (StrLit s)) (JSLitv (JSString s))) /\
	(v_rel (Conv (SOME (TypeStamp "true" bool_type_num)) []) (JSLitv (JSBool T))) /\
	(v_rel (Conv (SOME (TypeStamp "false" bool_type_num)) []) (JSLitv (JSBool F)))`;

val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  !env js_env. (!n v. nsLookup env (Short n) = SOME v ==> (?js_v. envLookup js_env n = SOME js_v
    /\ v_rel v js_v)) ==> env_rel env js_env`;

(*
val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  (!genv eid. env_rel genv nsEmpty <| scopes := [<| eid := eid; lexEnv := [] |>] |>) /\
  (!genv env js_st js_env. env_rel genv env scopes
    ==> env_rel genv env (SND (enter_scope js_st js_env))) /\
  (!genv env js_env x v js_v. env_rel genv env js_env /\ v_rel v js_v
    ==> env_rel genv (nsBind x v env) (envAssign js_env (x, js_v)))`;

val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  (!genv eid. env_rel genv nsEmpty <| eid := eid; lexEnv := [] |>) /\
  (!genv env js_st js_env eid. env_rel genv env scopes
    ==> env_rel genv env (flattenScopes eid (SND (enter_scope js_st js_env)).scopes)) /\
  (!genv env js_env eid eid' x v js_v. env_rel genv env (flattenScopes eid js_env.scopes)
    /\ v_rel v js_v
      ==> env_rel genv (nsBind x v env) (flattenScopes eid' (envAssign js_env (x, js_v)).scopes))`;
*)

val find_concat = Q.prove(`ALOOKUP l n ++ ALOOKUP l' n = ALOOKUP (l ++ l') n`, cheat);

val flattenScopeProof = Q.prove(`!env eid x. envLookup env x =
    scopeLookup (flattenScopes eid env.scopes) x`,
  Cases
    >> Induct_on `l`
    >> fs [scopesLookup_def, envLookup_def, flattenScopes_def, scopeLookup_def, mllistTheory.FIND_thm, find_concat]);
rw []


val nsLookup_def = fetch "namespace" "nsLookup_def";

`!env js_env x. env_rel env js_env /\
  nsLookup env (Short x) = NONE ==> envLookup js_env x = NONE`

fs []
>> rw []
>> Cases_on `js_env'`
>> fs [scopesLookup_def, flattenScopes_def]
>> Induct_on `l`
>> TRY (fs [scopesLookup_def] >> NO_TAC)
>> simp [Once env_rel_cases]
>> rw []
>> fs [envLookup_def, scopesLookup_def, scopeLookup_def, enter_scope_def, inc_scope_counter_def, nsLookup_def, nsEmpty_def, mllistTheory.FIND_thm, envAssign_def, flattenScopeProof]
>> rw []

Cases_on `l`

srw_tac [] [env_rel_cases]
metis_tac [env_rel_rules]

every_case_tac

val env_evaluate_proof = Q.prove(
  `!exps env st sem_env st' exps vs js_st js_env js_exps js_st' js_env' js_vs.
    env_rel env js_env /\
    compile_exp exps = SOME js_exps /\
    js_evaluate_exp js_st js_env js_exps = (js_st', js_env', JSRval js_vs)
      ==> env_rel env js_env'`,
  cheat);

Cases_on `js_env'`
>> Cases_on `env`
>> fs [env_rel_cases, v_rel_cases, nsLookup_def, evaluate_def, js_evaluate_exp_def, envLookup_def, scopesLookup_def, scopeLookup_def]
>> rpt strip_tac
>> rw []
>> Induct_on `l`
>> fs [env_rel_cases, v_rel_cases, nsLookup_def, evaluate_def, js_evaluate_exp_def, envLookup_def, scopesLookup_def, scopeLookup_def]
>> rw []
>> Induct_on `l0`
>> fs [env_rel_cases, v_rel_cases, nsLookup_def, evaluate_def, js_evaluate_exp_def, envLookup_def, scopesLookup_def, scopeLookup_def]
>> rw []

`!exps js_exps vs st st' sem_env js_env.
	(env_rel sem_env.v js_env /\
  compile_exp exps = SOME js_exps /\
	evaluate st sem_env exps = (st', Rval vs))
		==> ?js_st js_vs js_st' js_env'.
			(js_evaluate_exp js_st js_env js_exps = (js_st', js_env', JSRval js_vs) /\
      LIST_REL v_rel vs js_vs
      /\ env_rel sem_env.v js_env')`;

recInduct compile_exp_ind >> rpt strip_tac
  >> TRY (fs [evaluate_def, js_evaluate_exp_def, compile_exp_def]
    >> rveq
    >> fs [evaluate_def, js_evaluate_exp_def, compile_exp_def]
    >> NO_TAC)
  >> TRY (rename1 `compile_exp [Lannot _ _] = _`
    >> fs [compile_exp_def, evaluate_def]
    >> rpt (first_x_assum (drule) >> strip_tac)
    >> asm_exists_tac
    >> fs []
    >> NO_TAC)

fs [compile_exp_def, compile_op_def, evaluate_def]
>> every_case_tac
>> fs [compile_exp_def, compile_op_def, evaluate_def]
>> rveq
>> pop_assum drule
>> rpt(disch_then drule)
>> rpt strip_tac
>> first_x_assum drule
>> rpt(disch_then drule)
>> rpt strip_tac
>> imp_res_tac compile_exp_length_proof
>> cases_on `x` >> fs [js_evaluate_exp_def]
>> rename1 `js_evaluate_exp _ _ [_] = (js_st1, js_env1, JSRval js_vs1)`
>> qexists_tac `js_st`
>> fs []


rpt (qpat_x_assum `_ = _` (mp_tac o REWRITE_RULE[quantHeuristicsTheory.PAIR_EQ_EXPAND]))
>> rpt strip_tac
>> rveq
>> fs [js_evaluate_exp_def]
>> rpt (first_x_assum (drule) >> strip_tac)
>> Cases_on `x`
>- (imp_res_tac compile_exp_length_proof
  >> fs [])
>> fs [js_evaluate_exp_def, v_rel_cases, env_rel_cases, env_evaluate_proof]

rpt (qpat_x_assum `_ = JSRval _` (assume_tac o GSYM))
>> asm_exists_tac
>> fs []
>> imp_res_tac evaluate_length_proof
>> rveq
>> fs []
>> rw []
>> metis_tac [SING_HD]

fs [js_evaluate_exp_def, fix_clock_js_evaluate_exp]
qexists_tac `js_st`
fs []


fs [compile_exp_def, evaluate_def]
every_case_tac >> fs []
rveq
first_x_assum (qspec_then `h` assume_tac)
fs [evaluate_def]
every_case_tac
metis_tac []

imp_res_tac evaluate_length_proof
imp_res_tac fix_clock_js_evaluate_exp
imp_res_tac compile_exp_length_proof

rw []
fs []
fs [evaluate_def]
fs [js_evaluate_exp_def]
fs [compile_exp_def]
fs [trd_def]
every_case_tac
rveq
rfs []
simp []

fs [compile_exp_def]
every_case_tac
fs []
rveq
first_x_assum (qspec_then `h` assume_tac)
fs [evaluate_def]
first_x_assum (qspec_then `a` assume_tac)
first_x_assum (qspec_then `a'` assume_tac)
first_x_assum (qspec_then `st` assume_tac)
first_x_assum (qspec_then `q` assume_tac)
rfs []
Cases_on `x`
fs []
asm_exists_tac
rveq
fs [js_evaluate_exp_def, trd_def]
imp_res_tac evaluate_length_proof
imp_res_tac fix_clock_js_evaluate_exp
imp_res_tac compile_exp_length_proof
rw []

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

