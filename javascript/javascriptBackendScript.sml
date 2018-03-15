open preamble javascriptAstTheory astTheory stringTheory miscTheory;

val _ = new_theory"javascriptBackend";

val toList_def = Define `toList h = [h]`;

val UNDEFINED_def = Define `UNDEFINED = JSVar "undefined"`;

val sequenceOption_def = Define `
  sequenceOption l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val addVarPrefix_def = Define `
	addVarPrefix name = "cml_" ++ name`;

val addGenPrefix_def = Define `
	addGenPrefix name = "cmlg_" ++ name`;

val addTypePrefix_def = Define `
	addTypePrefix name = "cmltype_" ++ name`;

val exp_size_not_zero = Q.prove(`!exp. 0 < exp_size exp`, Cases >> rw [exp_size_def]);

val compile_lit_def = Define `
	(compile_lit (IntLit i) = JSBigInt i) /\
	(compile_lit (Char c) = JSString [c]) /\
	(compile_lit (StrLit s) = JSString s)`;

val compile_op_def = Define `
	compile_op op [a; b] = JSBop op a b`;

val compile_var'_def = Define `
	compile_var' op = JSAFun [JSBVar (addGenPrefix "a")]
		[JSReturn (JSAFun [JSBVar (addGenPrefix "b")]
			[JSReturn (JSBop op (JSVar (addGenPrefix "a")) (JSVar (addGenPrefix "b")))])]`;

val compile_var_def = Define `
	(compile_var "+" = compile_var' JSPlus) /\
	(compile_var "-" = compile_var' JSMinus) /\
	(compile_var "*" = compile_var' JSTimes) /\
	(compile_var "/" = compile_var' JSDivide) /\
	(compile_var "<" = compile_var' JSLt) /\
	(compile_var "<=" = compile_var' JSLeq) /\
	(compile_var ">" = compile_var' JSGt) /\
	(compile_var ">=" = compile_var' JSGeq) /\
	(compile_var "!" = JSAFun [JSBVar (addGenPrefix "a")]
			[JSReturn (JSObjectRetrieve (JSVar (addGenPrefix "a")) (addGenPrefix "v"))]) /\
	(compile_var ":=" = JSAFun [JSBVar (addGenPrefix "a")] [JSReturn (JSAFun [JSBVar (addGenPrefix "b")]
			[JSExp (JSObjectAssign (JSVar (addGenPrefix "a")) (addGenPrefix "v") (JSVar (addGenPrefix "b")));
				JSReturn UNDEFINED])]) /\
	(compile_var "=" = compile_var' JSEq) /\
	(compile_var "<>" = compile_var' JSNeq) /\
	(compile_var name = JSVar (addVarPrefix name))`;

val compile_con_def = Define `
	(compile_con (SOME (Short "true")) _ = SOME [JSLit (JSBool T)]) /\
	(compile_con (SOME (Short "false")) _ = SOME [JSLit (JSBool F)]) /\
	(compile_con (SOME (Short "nil")) _ = SOME [JSArray []]) /\
	(compile_con (SOME (Short "::")) [head; tail] = SOME [JSArray [head; JSRest tail]]) /\
	(compile_con NONE exps = SOME [JSObjectCreate [addGenPrefix "tuple", SOME (JSArray exps)]]) /\
	(compile_con (SOME (Short t)) exps = SOME [JSNew (JSVar (addTypePrefix t)) [JSArray exps]])`;

val compile_pat_def = tDefine "compile_pat" `
	(compile_pat Pany = JSObjectCreate ["pany", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pvar _) = JSObjectCreate ["pvar", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Plit lit) = JSObjectCreate ["plit", SOME (JSLit (compile_lit lit))]) /\
	(compile_pat (Pref pat) = JSObjectCreate ["pref", SOME (compile_pat pat)]) /\
	(compile_pat (Pcon NONE pats) = JSObjectCreate ["tuple", SOME (JSArray (MAP compile_pat pats))]) /\
	(compile_pat (Pcon (SOME (Short "::")) [l1; l2]) = JSObjectCreate
		[("array", SOME (JSLit (JSBool T)));
		("head", SOME (compile_pat l1)); ("tail", SOME (compile_pat l2))]) /\
	(compile_pat (Pcon (SOME (Short "nil")) _) = JSObjectCreate ["array", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pcon (SOME (Short cls)) fields) =
		JSObjectCreate [("cls", SOME (JSVar (addTypePrefix cls)));
			("fields", SOME (JSArray (MAP compile_pat fields)))])`
	cheat;

val create_deconstructor_def = tDefine "create_deconstructor" `
	(create_deconstructor Pany = JSBDiscard) /\
	(create_deconstructor (Pvar name) = JSBVar (addVarPrefix name)) /\
	(create_deconstructor (Plit _) = JSBVar (addGenPrefix "_")) /\
	(create_deconstructor (Pref pat) =
		JSBObject [addGenPrefix "v", SOME (create_deconstructor pat)]) /\
	(create_deconstructor (Pcon NONE pats) =
		JSBObject [addGenPrefix "tuple", SOME (JSBArray (MAP create_deconstructor pats))]) /\
	(create_deconstructor (Pcon (SOME (Short "::")) [l1; l2]) =
		JSBArray [create_deconstructor l1; JSBRest (create_deconstructor l2)]) /\
	(create_deconstructor (Pcon (SOME (Short "nil")) _) = JSBArray []) /\
	(create_deconstructor (Pcon _ fields) = 
		JSBObject [addGenPrefix "fields", SOME (JSBArray (MAP create_deconstructor fields))])`
	cheat;

(*
val create_deconstructor_def = tDefine "create_deconstructor" `
	(create_deconstructor dc Pany = (dc + 1, JSBVar (addGenPrefix ("_" ++ toString dc)))) /\
	(create_deconstructor dc (Pvar name) = (dc, JSBVar (addVarPrefix name))) /\
	(create_deconstructor dc (Plit _) = (dc + 1, JSBVar (addGenPrefix ("_" ++ toString dc)))) /\
	(create_deconstructor dc (Pref pat) =
		let (dc, deconstructor) = create_deconstructor dc pat
		in (dc, JSBObject [addGenPrefix "v", SOME deconstructor])) /\
	(create_deconstructor dc (Pcon NONE pats) =
		let (dc, des) = FOLDL
			(\r f. let (dc, d) = create_deconstructor (FST r) f in (dc, SND r ++ [d]))
			(dc, []) pats
		in (dc, JSBObject [addGenPrefix "tuple", SOME (JSBArray des)])) /\
	(create_deconstructor dc (Pcon (SOME (Short "::")) [l1; l2]) = let
			(dc, d1) = create_deconstructor dc l1;
			(dc, d2) = create_deconstructor dc l2
		in (dc, JSBArray [d1; JSBRest d2])) /\
	(create_deconstructor dc (Pcon (SOME (Short "nil")) _) = (dc, JSBArray [])) /\
	(create_deconstructor dc (Pcon _ fields) = 
		let (dc, des) = FOLDL
			(\r f. let (dc, d) = create_deconstructor (FST r) f in (dc, SND r ++ [d]))
			(dc, []) fields
		in (dc, JSBObject [addGenPrefix "fields", SOME (JSBArray des)]))`
	cheat;
*)

val errorStm_def = Define `
	errorStm t = JSApp (JSAFun [] [JSThrow t]) []`;

val compile_pattern_match_def = Define `
	(compile_pattern_match [] _ = errorStm (JSNew (JSVar "Error")
			[JSLit (JSString "Pattern and expression have incompatible types")])) /\
	(compile_pattern_match ((p, exp)::ps) content = JSConditional
			(JSApp (JSVar "doesmatch") [compile_pat p; content])
			(JSApp (JSAFun [create_deconstructor p] [JSReturn exp]) [content])
			(compile_pattern_match ps content))`;

val create_assignment_def = Define `
	create_assignment pat exp = JSIf (JSApp (JSVar "doesmatch") [compile_pat pat; exp])
			(JSVarDecl (create_deconstructor pat) exp)
			(JSThrow (JSNew (JSVar "Error") [JSLit (JSString "Exception- Bind raised")]))`;

val type_class_def_def = Define `
	type_class_def extends name = let
			constructor = ("constructor", [addGenPrefix "fields"],
				(JSObjectAssign (JSVar "this") (addGenPrefix "fields") (JSVar (addGenPrefix "fields"))))
		in JSVarDecl
			(JSBVar name)
			(JSClass NONE extends (if IS_NONE extends then [constructor] else []))`;

val compile_type_def_def = Define `
	compile_type_def (_, name, fields) = type_class_def NONE (addTypePrefix name) ::
		MAP (type_class_def (SOME (addTypePrefix name)) o addTypePrefix o FST) fields`;

val compile_defns = Defn.Hol_multi_defns `
	(compile_exp [] = SOME []) /\
	(compile_exp (exp1::exp2::exps) = (OPTION_MAP FLAT o sequenceOption o MAP (compile_exp o toList))
		(exp1::exp2::exps)) /\
	(compile_exp [Lannot exp _] = compile_exp [exp]) /\
	(compile_exp [Lit lit] = SOME [JSLit (compile_lit lit)]) /\
	(compile_exp [Var (Short name)] = SOME [compile_var name]) /\
	(compile_exp [Con id exps] = OPTION_BIND (compile_exp exps) (compile_con id)) /\
	(compile_exp [If condition ifexp elseexp] = OPTION_MAP
			(\l. [JSConditional (EL 0 l) (EL 1 l) (EL 2 l)])
			(compile_exp [condition; ifexp; elseexp])) /\
  (compile_exp [App Opapp exps] = OPTION_MAP (\l. [JSApp (HD l) (TL l)]) (compile_exp exps)) /\
	(compile_exp [Fun par exp] = OPTION_MAP
			(toList o (JSAFun [JSBVar (addVarPrefix par)]) o toList o JSReturn o HD)
			(compile_exp [exp])) /\
	(compile_exp [App Opref exps] = OPTION_MAP (\l. [JSObjectCreate [addGenPrefix "v", SOME (HD l)]]) (compile_exp exps)) /\
  (compile_exp [Let (SOME name) exp1 exp2] =
    OPTION_MAP (\es. [JSApp (JSAFun [JSBVar (addVarPrefix name)] [JSReturn (LAST es)]) [HD es]])
			(compile_exp [exp1; exp2])) /\
  (compile_exp [Letrec funs exp] =
		let
			funToJSFun = (\(name, par, body). OPTION_MAP
				(\body'. JSFun (addVarPrefix name) [JSBVar (addVarPrefix par)] [JSReturn (HD body')])
				(compile_exp [body]));
			funs' = sequenceOption (MAP funToJSFun funs);
			letinConst = (\jsexp funs''.
				[JSApp (JSAFun (MAP (JSBVar o addVarPrefix o FST) funs) [JSReturn (HD jsexp)]) funs''])
		in OPTION_MAP2 letinConst (compile_exp [exp]) funs') /\
	(compile_exp [Log And exp1 exp2] = let exps = compile_exp [exp1; exp2]
		in OPTION_MAP (toList o compile_op JSAnd) exps) /\
	(compile_exp [Log Or exp1 exp2] = let exps = compile_exp [exp1; exp2]
		in OPTION_MAP (toList o compile_op JSOr) exps) /\
	(compile_exp [Mat exp cases] = let
			cases' = sequenceOption (MAP (\c. OPTION_MAP (\e. (FST c, HD e)) (compile_exp [SND c])) cases);
			exp' = OPTION_MAP HD (compile_exp [exp])
		in OPTION_MAP2 (\c e. toList (compile_pattern_match c e)) cases' exp') /\
	(compile_exp [Raise exp] = OPTION_MAP (toList o errorStm o HD) (compile_exp [exp])) /\
	(compile_exp [Handle exp cases] = let
			cases' = sequenceOption (MAP (\c. OPTION_MAP (\e. (FST c, HD e)) (compile_exp [SND c])) cases);
			exp' = OPTION_MAP HD (compile_exp [exp])
		in OPTION_MAP2
			(\c e. [JSApp (JSAFun [] [JSTryCatch [JSExp e] (JSBVar (addGenPrefix "error"))
				[JSReturn (compile_pattern_match c (JSVar (addGenPrefix "error")))]]) []])
			cases' exp') /\
	(compile_exp _ = NONE) /\

	(compile_dec (Dlet _ pat exp) = OPTION_MAP
			(toList o (create_assignment pat) o HD) (compile_exp [exp])) /\
	(compile_dec (Dletrec _ defs) = let
				exps = MAP (\(_, _, exp). exp) defs;
				zipped = OPTION_MAP (\jsexps. ZIP (defs, jsexps)) (compile_exp exps);
				replaced = OPTION_MAP (MAP (\((name, par, _), exp). (name, par, exp))) zipped;
			in OPTION_MAP (MAP
				(\(name, par, exp).
					JSVarDecl (JSBVar (addVarPrefix name)) (JSAFun [JSBVar (addVarPrefix par)] [JSReturn exp])))
				replaced) /\
	(compile_dec (Dtype _ type_defs) = SOME (FLAT (MAP compile_type_def type_defs))) /\
	(compile_dec (Dexn _ name _) = SOME [type_class_def NONE (addTypePrefix name)]) /\
	(compile_dec _ = NONE)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) compile_defns;
val compile_exp_def = fetch "-" "compile_exp_def";
val compile_dec_def = fetch "-" "compile_dec_def";

(*
	((WF_REL_TAC `measure (SUM o MAP exp_size)`)
		>> rpt strip_tac
		>> fs [exp_size_def, exp_size_not_zero]
		>> qspec_then `exp2` assume_tac exp_size_not_zero
		>> fs []
		>> Induct_on `exps`
		>> fs [exp_size_def]);

val compile_exp_ind = fetch "-" "compile_exp_ind";

val compile_exp_length_proof = Q.store_thm("compile_exp_length_proof",
  `!exps js_exps. (compile_exp exps) = SOME js_exps ==> LENGTH exps = LENGTH js_exps`,
	recInduct compile_exp_ind
		>> rpt strip_tac
		>> fs [compile_exp_def, toList_def]
		>> every_case_tac
		>> fs [compile_exp_def, toList_def]
		>> rveq
		>> fs [compile_exp_def, toList_def, compile_con_def]
		>> cheat);
*)

val compile_top_def = Define `
	(compile_top (Tdec dec) = compile_dec dec) /\
	(compile_top _ = NONE)`;

val imports_def = Define `
	imports = [
		JSConst (JSBVar "bigInt") (JSApp (JSVar "require") [JSLit (JSString "./BigInteger.min.js")]);
		JSConst (JSBObject [("cmljs_eq", NONE);("doesmatch", NONE)])
			(JSApp (JSVar "require") [JSLit (JSString "./patternmatch.js")])]`;

val compile_prog_def = Define `
	compile_prog tops = OPTION_MAP ($++ imports o FLAT) (sequenceOption (MAP compile_top tops))`;

val _ = export_theory();

