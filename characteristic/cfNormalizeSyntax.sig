signature cfNormalizeSyntax = sig
  include Abbrev

  val full_normalise_prog_tm   : term
  val mk_full_normalise_prog   : term -> term
  val dest_full_normalise_prog : term -> term
  val is_full_normalise_prog   : term -> bool

  val full_normalise_tm   : term
  val mk_full_normalise   : term * term -> term
  val dest_full_normalise : term -> term * term
  val is_full_normalise   : term -> bool
end