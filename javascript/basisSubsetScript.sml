open basis ListProgTheory

val _ = new_theory "basisSubset";

max_print_depth := 11351351;

val _ = translation_extends "ListProg";

val basisSubset_st = get_ml_prog_state ();

val basisSubset_prog = basisSubset_st |> remove_snocs
  |> get_thm |> concl |> rator |> rator |> rator |> rand;

val basisSubset_def = Define `basisSubset = ^basisSubset_prog`;

val _ = export_theory();

