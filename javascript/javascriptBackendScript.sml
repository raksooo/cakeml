open preamble javascriptAstTheory astTheory stringTheory;

val _ = new_theory"javascriptBackend";

val toList_def = Define `toList h = [h]`;

val UNDEFINED_def = Define `UNDEFINED = JSVar "undefined"`;

val sequenceOption_def = Define `
  sequenceOption l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val addVarPrefix_def = Define `
	addVarPrefix name = "cml_" ++ name`;

val addGenPrefix_def = Define `
	addGenPrefix name = "cmlg_" ++ name`;

val exp_size_not_zero = Q.prove(`!exp. 0 < exp_size exp`, Cases >> rw [exp_size_def]);

val ata_lit_def = Define `
	(ata_lit (IntLit i) = JSBigInt i) /\
	(ata_lit (Char c) = JSString [c]) /\
	(ata_lit (StrLit s) = JSString s)`;

val ata_op_def = Define `
	ata_op op [a; b] = JSBop op a b`;

val ata_var'_def = Define `
	ata_var' op = JSAFun [JSBVar (addGenPrefix "a")]
		(JSAFun [JSBVar (addGenPrefix "b")]
			(JSBop op (JSVar (addGenPrefix "a")) (JSVar (addGenPrefix "b"))))`;

val ata_var_def = Define `
	(ata_var "+" = ata_var' JSPlus) /\
	(ata_var "-" = ata_var' JSMinus) /\
	(ata_var "*" = ata_var' JSTimes) /\
	(ata_var "/" = ata_var' JSDivide) /\
	(ata_var "<" = ata_var' JSLt) /\
	(ata_var "<=" = ata_var' JSLeq) /\
	(ata_var ">" = ata_var' JSGt) /\
	(ata_var ">=" = ata_var' JSGeq) /\
	(ata_var "!" = JSAFun [JSBVar (addGenPrefix "a")]
			(JSObjectRetrieve (JSVar (addGenPrefix "a")) (addGenPrefix "v"))) /\
	(ata_var ":=" = JSAFun [JSBVar (addGenPrefix "a")] (JSAFun [JSBVar (addGenPrefix "b")]
			(JSComma [JSObjectAssign (JSVar (addGenPrefix "a")) (addGenPrefix "v") (JSVar (addGenPrefix "b"));
				UNDEFINED]))) /\
	(ata_var name = JSVar (addVarPrefix name))`;

val ata_con_def = Define `
	(ata_con (SOME (Short "true")) _ = SOME [JSLit (JSBool T)]) /\
	(ata_con (SOME (Short "false")) _ = SOME [JSLit (JSBool F)]) /\
	(ata_con (SOME (Short "nil")) _ = SOME [JSArray []]) /\
	(ata_con (SOME (Short "::")) [head; tail] = SOME [JSArray [head; JSRest tail]]) /\
	(ata_con NONE exps = SOME [JSObjectCreate [addGenPrefix "tuple", SOME (JSArray exps)]]) /\
	(ata_con (SOME (Short t)) exps = SOME [JSNew (JSVar (addVarPrefix t)) [JSArray exps]])`;

val compile_pat_def = tDefine "compile_pat" `
	(compile_pat Pany = JSObjectCreate ["pany", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pvar _) = JSObjectCreate ["pvar", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Plit lit) = JSObjectCreate ["plit", SOME (JSLit (ata_lit lit))]) /\
	(compile_pat (Pref pat) = JSObjectCreate ["pref", SOME (compile_pat pat)]) /\
	(compile_pat (Pcon NONE pats) = JSObjectCreate ["tuple", SOME (JSArray (MAP compile_pat pats))]) /\
	(compile_pat (Pcon (SOME (Short "::")) [l1; l2]) = JSObjectCreate
		[("array", SOME (JSLit (JSBool T)));
		("head", SOME (compile_pat l1)); ("tail", SOME (compile_pat l2))]) /\
	(compile_pat (Pcon (SOME (Short "nil")) _) = JSObjectCreate ["array", SOME (JSLit (JSBool T))]) /\
	(compile_pat (Pcon (SOME (Short cls)) fields) = JSObjectCreate [("cls", SOME (JSVar (addVarPrefix cls)));
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

val compile_pattern_match_def = Define `
	(compile_pattern_match [] _ = JSNew (JSVar "Error")
			[JSLit (JSString "Pattern and expression have incompatible types")]) /\
	(compile_pattern_match ((p, exp)::ps) content = JSConditional
			(JSApp (JSVar "doesmatch") [compile_pat p; content])
			(JSApp (JSAFun [create_deconstructor p] exp) [content])
			(compile_pattern_match ps content))`;

val create_assignment_def = Define `
	create_assignment pat exp = JSIf (JSApp (JSVar "doesmatch") [compile_pat pat; exp])
			(JSVarDecl (create_deconstructor pat) exp)
			(JSThrow (JSNew (JSVar "Error") [JSLit (JSString "Exception- Bind raised")]))`;

val ata_exp_def = tDefine "ata_exp" `
	(ata_exp [] = SOME []) /\
	(ata_exp (exp1::exp2::exps) = (OPTION_MAP FLAT o sequenceOption o MAP (ata_exp o toList))
		(exp1::exp2::exps)) /\
	(ata_exp [Lannot exp _] = ata_exp [exp]) /\
	(ata_exp [Lit lit] = SOME [JSLit (ata_lit lit)]) /\
	(ata_exp [Var (Short name)] = SOME [ata_var name]) /\
	(ata_exp [Con id exps] = OPTION_BIND (ata_exp exps) (ata_con id)) /\
	(ata_exp [If condition ifexp elseexp] = OPTION_MAP
			(\l. [JSConditional (EL 0 l) (EL 1 l) (EL 2 l)])
			(ata_exp [condition; ifexp; elseexp])) /\

  (ata_exp [App Opapp exps] = OPTION_MAP (\l. [JSApp (HD l) (TL l)]) (ata_exp exps)) /\
	(ata_exp [Fun par exp] = OPTION_MAP
			(toList o (JSAFun [JSBVar (addVarPrefix par)]) o HD)
			(ata_exp [exp])) /\
	
	(ata_exp [App Opref exps] = OPTION_MAP (\l. [JSObjectCreate [addGenPrefix "v", SOME (HD l)]]) (ata_exp exps)) /\

  (ata_exp [Let (SOME name) exp1 exp2] =
    OPTION_MAP (\es. [JSApp (JSAFun [JSBVar (addVarPrefix name)] (LAST es)) [HD es]])
			(ata_exp [exp1; exp2])) /\
  (ata_exp [Letrec funs exp] =
		let
			funToJSFun = (\(name, par, body). OPTION_MAP
				(\body'. JSFun (addVarPrefix name) [JSBVar (addVarPrefix par)] (HD body'))
				(ata_exp [body]));
			funs' = sequenceOption (MAP funToJSFun funs);
			letinConst = (\jsexp funs''.
				[JSApp (JSAFun (MAP (JSBVar o addVarPrefix o FST) funs) (HD jsexp)) funs''])
		in OPTION_MAP2 letinConst (ata_exp [exp]) funs') /\

	(ata_exp [Log And exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSAnd) exps) /\
	(ata_exp [Log Or exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSOr) exps) /\

	(ata_exp [Mat exp cases] = let
			cases' = sequenceOption (MAP (\c. OPTION_MAP (\e. (FST c, HD e)) (ata_exp [SND c])) cases);
			exp' = OPTION_MAP HD (ata_exp [exp])
		in OPTION_MAP2 (\c e. toList (compile_pattern_match c e)) cases' exp') /\

	(ata_exp _ = NONE)`
	cheat;

(*
	((WF_REL_TAC `measure (SUM o MAP exp_size)`)
		>> rpt strip_tac
		>> fs [exp_size_def, exp_size_not_zero]
		>> qspec_then `exp2` assume_tac exp_size_not_zero
		>> fs []
		>> Induct_on `exps`
		>> fs [exp_size_def]);
*)

val ata_exp_ind = fetch "-" "ata_exp_ind";

val ata_exp_length_proof = Q.store_thm("ata_exp_length_proof",
  `!exps js_exps. (ata_exp exps) = SOME js_exps ==> LENGTH exps = LENGTH js_exps`,
	recInduct ata_exp_ind
		>> rpt strip_tac
		>> fs [ata_exp_def, toList_def]
		>> every_case_tac
		>> fs [ata_exp_def, toList_def]
		>> rveq
		>> fs [ata_exp_def, toList_def, ata_con_def]
		>> cheat);

val type_class_def_def = Define `
	type_class_def extends name = let
			constructor = ("constructor", [addGenPrefix "fields"],
				(JSObjectAssign (JSVar "this") (addGenPrefix "fields") (JSVar (addGenPrefix "fields"))));
			extends' = OPTION_MAP addVarPrefix extends
		in JSVarDecl
			(JSBVar (addVarPrefix name))
			(JSClass NONE extends' (if IS_NONE extends then [constructor] else []))`;

val ata_type_def_def = Define `
	ata_type_def (_, name, fields) = type_class_def NONE name ::
		MAP (type_class_def (SOME name) o FST) fields`;

val ata_dec_def = Define `
	(ata_dec (Dlet _ pat exp) = OPTION_MAP
			(toList o (create_assignment pat) o HD) (ata_exp [exp])) /\
	(ata_dec (Dletrec _ defs) = let
				exps = MAP (\(_, _, exp). exp) defs;
				zipped = OPTION_MAP (\jsexps. ZIP (defs, jsexps)) (ata_exp exps);
				replaced = OPTION_MAP (MAP (\((name, par, _), exp). (name, par, exp))) zipped;
			in OPTION_MAP (MAP
				(\(name, par, exp).
					JSVarDecl (JSBVar (addVarPrefix name)) (JSAFun [JSBVar (addVarPrefix par)] exp)))
				replaced) /\
	(ata_dec (Dtype _ type_defs) = SOME (FLAT (MAP ata_type_def type_defs))) /\
	(ata_dec _ = NONE)`;

val ata_top_def = Define `
	(ata_top (Tdec dec) = ata_dec dec) /\
	(ata_top _ = NONE)`;

val imports_def = Define `
	imports = [
		JSConst (JSBVar "bigInt") (JSApp (JSVar "require") [JSLit (JSString "./BigInteger.min.js")]);
		JSConst (JSBVar "doesmatch") (JSApp (JSVar "require") [JSLit (JSString "./patternmatch.js")])]`;

val ata_prog_def = Define `
	ata_prog tops = OPTION_MAP ($++ imports o FLAT) (sequenceOption (MAP ata_top tops))`;

val _ = export_theory();

