open preamble javascriptAstTheory javascriptSemanticsTheory astTheory stringTheory;

val _ = new_theory"javascriptBackend";

val toList_def = Define `toList h = [h]`;

val sequenceOption_def = Define `
  sequenceOption l = FOLDL (OPTION_MAP2 (\l' v. l' ++ [v])) (SOME []) l`;

val addVarPrefix_def = Define `
	addVarPrefix name = "cml_" ++ name`;

val addVarsPrefix_def = Define `
	addVarsPrefix names = MAP addVarPrefix names`;

val ata_op_def = Define `
	ata_op op [a; b] = JSBop op a b`;

val exp_size_not_zero = Q.prove(`!exp. 0 < exp_size exp`, Cases >> rw [exp_size_def]);

val ata_exp_def = tDefine "ata_exp" `
	(ata_exp [] = SOME []) /\
	(ata_exp (exp1::exp2::exps) = (OPTION_MAP FLAT o sequenceOption o MAP (ata_exp o toList))
		(exp1::exp2::exps)) /\
	(ata_exp [Lannot exp _] = ata_exp [exp]) /\
	(ata_exp [Var (Short name)] = SOME [JSVar (addVarPrefix name)]) /\
	(ata_exp [Con (SOME (Short b)) _] =
		if b = "true" then SOME [JSLit (JSBool T)]
		else if b = "false" then SOME [JSLit (JSBool F)]
		else NONE) /\
  (ata_exp [App Opapp exps] = OPTION_MAP (\l. [JSApp (HD l) (TL l)]) (ata_exp exps)) /\
	(ata_exp [Fun par exp] = OPTION_MAP (toList o (JSAFun [addVarPrefix par]) o HD) (ata_exp [exp])) /\
  (ata_exp [Let (SOME name) exp1 exp2] =
    OPTION_MAP (\es. [JSApp (JSAFun [addVarPrefix name] (LAST es)) [HD es]]) (ata_exp [exp1; exp2])) /\
	(ata_exp [Log And exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSAnd) exps) /\
	(ata_exp [Log Or exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in OPTION_MAP (toList o ata_op JSOr) exps) /\
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
		>> fs [ata_exp_def, toList_def]);

val ata_dec_def = Define `
	(ata_dec (Dlet _ Pany exp) = OPTION_MAP (toList o JSExp o HD) (ata_exp [exp])) /\
	(ata_dec (Dlet _ (Pvar name) exp) =
			OPTION_MAP (toList o (JSVar (addVarPrefix name)) o HD) (ata_exp [exp])) /\
	(ata_dec (Dletrec _ defs) = let
				exps = MAP (\(_, _, exp). exp) defs;
				zipped = OPTION_MAP (\jsexps. ZIP (defs, jsexps)) (ata_exp exps);
				replaced = OPTION_MAP (MAP (\((name, par, _), exp). (name, par, exp))) zipped;
			in OPTION_MAP (MAP
				(\(name, par, exp). JSVar (addVarPrefix name) (JSAFun [addVarPrefix par] exp)))
				replaced) /\
	(ata_dec _ = NONE)`;

val ata_top_def = Define `
	(ata_top (Tdec dec) = ata_dec dec) /\
	(ata_top _ = NONE)`;

val ata_prog_def = Define `
	ata_prog tops = OPTION_MAP FLAT (sequenceOption (MAP ata_top tops))`;

val _ = export_theory();

