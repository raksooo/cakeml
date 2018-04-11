open preamble jsAstTheory astTheory stringTheory miscTheory;

val _ = new_theory"jsBackend";

val toList_def = Define `toList h = [h]`;

val sequenceOption_def = Define `
  sequenceOption l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val addVarPrefix_def = Define `
	addVarPrefix name = "cml_" ++ name`;

val addGenPrefix_def = Define `
	addGenPrefix name = "cmlg_" ++ name`;

val addTypePrefix_def = Define `
	addTypePrefix name = "cmltype_" ++ name`;

val exp_size_not_zero = Q.prove(`!exp. 0 < exp_size exp`, Cases >> rw [exp_size_def]);

val js_unit_def = Define `
	js_unit = JSObject [addGenPrefix "tuple", SOME (JSArray [])]`;

val compile_lit_def = Define `
	(compile_lit (IntLit i) = JSLit (JSBigInt i)) /\
	(compile_lit (Char c) = JSObject [(addGenPrefix "char", SOME (JSLit (JSString [c])))]) /\
	(compile_lit (StrLit s) = JSLit (JSString s))`;

val compile_op_def = Define `
	compile_op op [a; b] = JSBop op a b`;

val compile_var'_def = Define `
	compile_var' op = JSAFun [JSBVar (addGenPrefix "a")]
		[JSReturn (JSAFun [JSBVar (addGenPrefix "b")]
			[JSReturn (JSBop op (JSVar (addGenPrefix "a")) (JSVar (addGenPrefix "b")))])]`;

val compile_var_def = Define `
	(compile_var "+" = compile_var' JSIntPlus) /\
	(compile_var "-" = compile_var' JSIntMinus) /\
	(compile_var "*" = compile_var' JSIntTimes) /\
	(compile_var "/" = compile_var' JSIntDivide) /\
	(compile_var "<" = compile_var' JSIntLt) /\
	(compile_var "<=" = compile_var' JSIntLeq) /\
	(compile_var ">" = compile_var' JSIntGt) /\
	(compile_var ">=" = compile_var' JSIntGeq) /\
	(compile_var "!" = JSAFun [JSBVar (addGenPrefix "a")]
			[JSReturn (JSObjectProp (JSVar (addGenPrefix "a")) (addGenPrefix "v"))]) /\
	(compile_var ":=" = JSAFun [JSBVar (addGenPrefix "a")] [JSReturn (JSAFun [JSBVar (addGenPrefix "b")]
			[JSExp (JSAssign (JSObjectProp (JSVar (addGenPrefix "a")) (addGenPrefix "v")) (JSVar (addGenPrefix "b")))])]) /\
	(compile_var "=" = compile_var' JSEq) /\
	(compile_var "<>" = compile_var' JSNeq) /\
	(compile_var name = JSVar (addVarPrefix name))`;

val compile_con_def = Define `
	(compile_con (SOME (Short "true")) _ = SOME [JSLit (JSBool T)]) /\
	(compile_con (SOME (Short "false")) _ = SOME [JSLit (JSBool F)]) /\
	(compile_con (SOME (Short "nil")) _ = SOME [JSArray []]) /\
	(compile_con (SOME (Short "::")) [head; tail] = SOME [JSArray [head; JSUop JSSpread tail]]) /\
	(compile_con NONE exps = SOME [JSObject [addGenPrefix "tuple", SOME (JSArray exps)]]) /\
	(compile_con (SOME (Short t)) exps = SOME [JSUop JSNew (JSApp (JSVar (addTypePrefix t)) [JSArray exps])])`;

val compile_pat_def = tDefine "compile_pat" `
	(compile_pat Pany = JSObject ["pany", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pvar _) = JSObject ["pvar", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Plit lit) = JSObject ["plit", SOME (compile_lit lit)]) /\
	(compile_pat (Pref pat) = JSObject ["pref", SOME (compile_pat pat)]) /\
	(compile_pat (Pcon NONE pats) = JSObject ["tuple", SOME (JSArray (MAP compile_pat pats))]) /\
	(compile_pat (Pcon (SOME (Short "::")) [l1; l2]) = JSObject
		[("array", SOME (JSLit (JSBool T)));
		("head", SOME (compile_pat l1)); ("tail", SOME (compile_pat l2))]) /\
	(compile_pat (Pcon (SOME (Short "nil")) _) = JSObject ["array", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pcon (SOME (Short cls)) fields) =
		JSObject [("cls", SOME (JSVar (addTypePrefix cls)));
			("fields", SOME (JSArray (MAP compile_pat fields)))]) /\
	(compile_pat (Ptannot pat _) = compile_pat pat)`
	cheat;

val create_deconstructor_def = tDefine "create_deconstructor" `
	(create_deconstructor ac Pany = (ac + 1, JSBVar (addGenPrefix ("_" ++ toString ac)))) /\
	(create_deconstructor ac (Pvar name) = (ac, JSBVar (addVarPrefix name))) /\
	(create_deconstructor ac (Plit _) = (ac + 1, JSBVar (addGenPrefix ("_" ++ toString ac)))) /\
	(create_deconstructor ac (Pref pat) =
		let (ac', deconstructor) = create_deconstructor ac pat
		in (ac', JSBObject [addGenPrefix "v", SOME deconstructor])) /\
	(create_deconstructor ac (Pcon NONE pats) =
		let (ac'', deconstructors) = FOLDL
			(\r f. let (ac', d) = create_deconstructor (FST r) f in (ac', SND r ++ [d]))
			(ac, []) pats
		in (ac'', JSBObject [addGenPrefix "tuple", SOME (JSBArray deconstructors)])) /\
	(create_deconstructor ac (Pcon (SOME (Short "nil")) []) = (ac, JSBArray [])) /\
	(create_deconstructor ac (Pcon (SOME (Short "::")) [l1; l2]) = let
			(ac', d1) = create_deconstructor ac l1;
			(ac'', d2) = create_deconstructor ac' l2
		in (ac'', JSBArray [d1; JSBRest d2])) /\
	(create_deconstructor ac (Pcon _ fields) = 
		let (ac'', deconstructors) = FOLDL
			(\r f. let (ac', d) = create_deconstructor (FST r) f in (ac', SND r ++ [d]))
			(ac, []) fields
		in (ac'', JSBObject [addGenPrefix "fields", SOME (JSBArray deconstructors)])) /\
	(create_deconstructor ac (Ptannot pat _) = create_deconstructor ac pat)`
	cheat;

val errorStm_def = Define `
	errorStm t = JSApp (JSAFun [] [JSThrow t]) []`;

val compile_pattern_match_def = Define `
	(compile_pattern_match [] _ = errorStm (JSUop JSNew (JSApp (JSVar "Error")
			[JSLit (JSString "Exception- Bind raised")]))) /\
	(compile_pattern_match ((p, exp)::ps) content = JSConditional
			(JSApp (JSVar "cmljs_doesmatch") [compile_pat p; content])
			(JSApp (JSAFun [SND (create_deconstructor 0 p)] [JSReturn exp]) [content])
			(compile_pattern_match ps content))`;

val create_assignment_def = Define `
	create_assignment pat exp = JSIf (JSApp (JSVar "cmljs_doesmatch") [compile_pat pat; exp])
			(JSVarDecl (SND (create_deconstructor 0 pat)) exp)
			(JSThrow (JSUop JSNew (JSApp (JSVar "Error") [JSLit (JSString "Exception- Bind raised")])))`;

val type_class_def_def = Define `
	type_class_def extends name = let
			constructor = ("constructor", [addGenPrefix "fields"],
				JSExp (JSAssign (JSObjectProp (JSVar "this") (addGenPrefix "fields")) (JSVar (addGenPrefix "fields"))))
		in JSVarDecl
			(JSBVar name)
			(JSClass NONE extends (if IS_NONE extends then [constructor] else []))`;

val compile_type_def_def = Define `
	compile_type_def (_, name, fields) = type_class_def NONE (addTypePrefix name) ::
		MAP (type_class_def (SOME (addTypePrefix name)) o addTypePrefix o FST) fields`;

val compile_app_def = tDefine "compile_app" `
	(compile_app Opref (exp::_) = SOME [JSObject [addGenPrefix "v", SOME exp]]) /\
	(compile_app Opassign (exp1::exp2::_) = SOME [JSBop JSComma
		(JSAssign (JSObjectProp exp1 (addGenPrefix "v")) exp2)
		js_unit]) /\
	(compile_app Equality exps = SOME [JSApp (JSVar "cmljs_eq") exps]) /\
	(compile_app (Opn Plus) (exp1::exp2::_) = SOME [JSBop JSIntPlus exp1 exp2]) /\
	(compile_app (Opn Minus) (exp1::exp2::_) = SOME [JSBop JSIntMinus exp1 exp2]) /\
	(compile_app (Opn Times) (exp1::exp2::_) = SOME [JSBop JSIntTimes exp1 exp2]) /\
	(compile_app (Opn Divide) (exp1::exp2::_) = SOME [JSBop JSIntDivide exp1 exp2]) /\
	(compile_app (Opn Modulo) (exp1::exp2::_) = SOME [JSBop JSIntModulo exp1 exp2]) /\
	(compile_app (Opb Lt) (exp1::exp2::_) = SOME [JSBop JSIntLt exp1 exp2]) /\
	(compile_app (Opb Leq) (exp1::exp2::_) = SOME [JSBop JSIntLeq exp1 exp2]) /\
	(compile_app (Opb Gt) (exp1::exp2::_) = SOME [JSBop JSIntGt exp1 exp2]) /\
	(compile_app (Opb Geq) (exp1::exp2::_) = SOME [JSBop JSIntGeq exp1 exp2]) /\
	(compile_app (FFI name) exps = SOME [JSApp (JSVar name) exps]) /\
	(compile_app Ord (exp1::_) =
		SOME [JSApp (JSObjectProp (JSObjectProp exp1 (addGenPrefix "char")) "charCodeAt") []]) /\
	(compile_app Chr exps = SOME [JSObject
		[(addGenPrefix "char"), SOME (JSApp (JSObjectProp (JSVar "String") "fromCharCode") exps)]]) /\
	(compile_app (Chopb opb) exps = compile_app (Opb opb) exps) /\
	(compile_app Strlen (exp1::_) = SOME [JSObjectProp exp1 "length"]) /\
	(compile_app Aalloc (exp1::exp2::_) = SOME [JSObject [addGenPrefix "array",
		SOME (JSApp (JSObjectProp (JSApp (JSUop JSNew (JSVar "Array"))
			[JSApp (JSObjectProp exp1 "toJSNumber") []]) "fill") [exp2])]]) /\
	(compile_app AallocEmpty _ = SOME [JSObject [addGenPrefix "array", SOME (JSArray [])]]) /\
	(compile_app Alength (exp::_) =
		SOME [JSObjectProp (JSObjectProp exp (addGenPrefix "array")) "length"]) /\
	(compile_app Aupdate (exp1::exp2::exp3::_) = SOME [JSBop JSComma
		(JSAssign (JSIndex (JSObjectProp exp1 (addGenPrefix "array"))
			(JSApp (JSObjectProp exp2 "toJSNumber") [])) exp3)
		js_unit]) /\
	(compile_app Asub (exp1::exp2::_) = SOME [JSIndex (JSObjectProp exp1 (addGenPrefix "array"))
			(JSApp (JSObjectProp exp2 "toJSNumber") [])]) /\
	(compile_app _ _ = NONE)` cheat;

val compile_defns = Defn.Hol_multi_defns `
	(compile_exp [] = SOME []) /\
	(compile_exp (exp1::exp2::exps) = (OPTION_MAP FLAT o sequenceOption o MAP (compile_exp o toList))
		(exp1::exp2::exps)) /\
	(compile_exp [Lannot exp _] = compile_exp [exp]) /\
	(compile_exp [Tannot exp _] = compile_exp [exp]) /\
	(compile_exp [Lit lit] = SOME [compile_lit lit]) /\
	(compile_exp [Var (Short name)] = SOME [compile_var name]) /\
	(compile_exp [Con id exps] = OPTION_BIND (compile_exp exps) (compile_con id)) /\
	(compile_exp [If condition ifexp elseexp] = OPTION_MAP
			(\l. [JSConditional (EL 0 l) (EL 1 l) (EL 2 l)])
			(compile_exp [condition; ifexp; elseexp])) /\
  (compile_exp [App Opapp exps] = OPTION_MAP (\l. [JSApp (HD l) (TL l)]) (compile_exp exps)) /\
	(compile_exp [Fun par exp] = OPTION_MAP
			(toList o (JSAFun [JSBVar (addVarPrefix par)]) o toList o JSReturn o HD)
			(compile_exp [exp])) /\
	(compile_exp [App op exps] = OPTION_CHOICE (OPTION_BIND (compile_exp exps) (compile_app op)) (SOME [Exp_not_compiled (App op exps)])) /\
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
	(compile_exp [exp] = SOME [Exp_not_compiled exp]) /\

	(compile_dec (Dlet _ (Pvar name) exp) = OPTION_MAP
			(toList o JSVarDecl (JSBVar (addVarPrefix name)) o HD) (compile_exp [exp])) /\
	(compile_dec (Dlet _ Pany exp) = OPTION_MAP
			(toList o JSVarDecl (JSBVar (addGenPrefix "_")) o HD) (compile_exp [exp])) /\
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
	(compile_dec dec = SOME [Dec_not_compiled dec])`;

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
	(compile_top top = SOME [Top_not_compiled top])`;

val imports_def = Define `
	imports = [
		JSVarDecl (JSBVar "bigInt") (JSApp (JSVar "require") [JSLit (JSString "./BigInteger.min.js")]);
		JSVarDecl (JSBObject [("cmljs_append", NONE);("cmljs_eq", NONE);("cmljs_doesmatch", NONE)])
			(JSApp (JSVar "require") [JSLit (JSString "./cmljs_utils.js")])]`;

val compile_prog_def = Define `
	compile_prog tops = OPTION_MAP ($++ imports o FLAT) (sequenceOption (MAP compile_top tops))`;

val compile_no_imports_def = Define `
	compile_no_imports tops = OPTION_MAP FLAT (sequenceOption (MAP compile_top tops))`;

val _ = export_theory();

