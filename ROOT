session "Bounded_Operators-Prerequisites" = "HOL-Analysis" +
  sessions "HOL-Library" "Jordan_Normal_Form" "HOL-Analysis" "HOL-Nonstandard_Analysis" "Real_Impl" "HOL-Types_To_Sets"
  theories 
    "HOL-Library.Adhoc_Overloading" "Jordan_Normal_Form.Conjugate"
	   "HOL-Library.Rewrite" "HOL-ex.Sketch_and_Explore"
	   "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
     Real_Impl.Real_Impl Jordan_Normal_Form.Matrix
     "HOL-Types_To_Sets.Types_To_Sets"

session Bounded_Operators = "Bounded_Operators-Prerequisites" +
  options [record_proofs=1, document = pdf, document_output = "output", 
           document_variants = "document:outline=/proof,/ML",
           quick_and_dirty = true]
  theories All
  document_files "root.tex"
