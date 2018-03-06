open preamble javascriptAstTheory javascriptSemanticsTheory astTheory stringTheory;

val _ = new_theory"javascriptBackend";

val toList_def = Define `toList h = [h]`;

val sequence_def = Define `
  sequence l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val ata_op_def = Define `
	ata_op op [a; b] = JSBop op a b`;

val exp_size_not_zero = Q.prove(`!exp. 0 < exp_size exp`, Cases >> rw [exp_size_def]);

val ata_exp_def = tDefine "ata_exp" `
	(ata_exp [] = SOME []) /\
	(ata_exp (exp1::exp2::exps) = case ata_exp [exp1] of
		| SOME [jsexp] => (case ata_exp (exp2 :: exps) of
				| SOME jsexps => SOME (jsexp :: jsexps)
				| NONE => NONE)
		| _ => NONE) /\
	(ata_exp [Lannot exp _] = ata_exp [exp]) /\
	(ata_exp [Var (Short name)] = SOME [JSVar ("js_" ++ name)]) /\
	(ata_exp [Con (SOME (Short b)) _] =
		if b = "true" then SOME [JSLit (JSBool T)]
		else if b = "false" then SOME [JSLit (JSBool F)]
		else NONE) /\
  (ata_exp [App Opapp exps] = OPTION_MAP (\l. [JSApp (HD l) (TL l)]) (ata_exp exps)) /\
	(ata_exp [Fun par exp] = OPTION_MAP (toList o (JSAFun [par]) o HD) (ata_exp [exp])) /\
  (ata_exp [Let (SOME name) exp1 exp2] =
    OPTION_MAP (\es. [JSApp (JSAFun [name] (LAST es)) [HD es]]) (ata_exp [exp1; exp2])) /\
	(ata_exp [Log And exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSAnd) exps) /\
	(ata_exp [Log Or exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSOr) exps) /\
	(ata_exp _ = NONE)`
	((WF_REL_TAC `measure (SUM o MAP exp_size)`)
		>> rpt strip_tac
		>> fs [exp_size_def, exp_size_not_zero]
		>> qspec_then `exp2` assume_tac exp_size_not_zero
		>> fs []
		>> Induct_on `exps`
		>> fs [exp_size_def]);

val ata_exp_ind = fetch "-" "ata_exp_ind";

val ata_exp_length_proof = Q.store_thm("ata_exp_length_proof",
  `!exps js_exps. (ata_exp exps) = SOME js_exps ==> LENGTH exps = LENGTH js_exps`,
	recInduct ata_exp_ind
		>> rpt strip_tac
		>> fs [ata_exp_def, toList_def]
		>> every_case_tac
		>> fs [ata_exp_def, toList_def]
		>> rveq
		>> fs [ata_exp_def, toList_def]);

val ata_dec_def = Define `
	(ata_dec (Dlet _ Pany exp) = OPTION_MAP (toList o JSExp o HD) (ata_exp [exp])) /\
	(ata_dec (Dlet _ (Pvar name) exp) =
			OPTION_MAP (toList o (JSLet ("js_" ++ name)) o HD) (ata_exp [exp])) /\
	(ata_dec (Dletrec _ defs) = let
				exps = MAP (\(_, _, exp). exp) defs;
				zipped = OPTION_MAP (\jsexps. ZIP (defs, jsexps)) (ata_exp exps);
				replaced = OPTION_MAP (MAP (\((name, par, _), exp). (name, par, exp))) zipped;
			in OPTION_MAP (MAP (\(name, par, exp). JSLet name (JSAFun [par] exp))) replaced) /\
	(ata_dec _ = NONE)`;

val ast_to_ast_def = Define `
	(ast_to_ast [] = SOME []) /\
	(ast_to_ast (dec::decs) = case ata_dec dec of
		| SOME dec' => (case ast_to_ast decs of
				| SOME decs' => SOME (dec' ++ decs')
				| NONE => NONE)
		| NONE => NONE)`;

val _ = export_theory();

