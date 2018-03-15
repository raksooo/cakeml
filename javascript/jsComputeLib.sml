structure jsComputeLib = struct
open preamble javascriptBackendTheory prettyPrintTheory

	val add_ata_compset = computeLib.extend_compset [computeLib.Defs [
			compile_exp_def,
			compile_dec_def,
			exp_toString_def
		]]
	val jseval = computeLib.compset_conv computeLib.the_compset [computeLib.Extenders [add_ata_compset]]

end

