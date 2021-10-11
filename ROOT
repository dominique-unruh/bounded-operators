session "Complex_Bounded_Operators-Prerequisites" in "fake-session-dir/1" = "HOL-Analysis" +
  sessions "HOL-Library" "Jordan_Normal_Form" "HOL-Analysis"
           "Real_Impl" "HOL-Types_To_Sets" "Banach_Steinhaus" "Containers"
  theories
     "HOL-Library.Adhoc_Overloading" "Jordan_Normal_Form.Conjugate"
     "HOL-Library.Rewrite" "HOL-ex.Sketch_and_Explore"
     Real_Impl.Real_Impl Jordan_Normal_Form.Matrix
     "HOL-Types_To_Sets.Types_To_Sets" Jordan_Normal_Form.Matrix_Kernel
     "Banach_Steinhaus.Banach_Steinhaus" "Containers.Containers_Auxiliary"
     "Jordan_Normal_Form.Matrix_Impl"
    
session "Complex_Bounded_Operators-Extra" in extra = "Complex_Bounded_Operators-Prerequisites" +
  options [document = pdf, document_output = "output", 
           document_variants = "document:outline=/proof,/ML"]
  theories Extra_General Extra_Vector_Spaces Extra_Ordered_Fields Extra_Pretty_Code_Examples

session Complex_Bounded_Operators2 = "Complex_Bounded_Operators-Extra" +
  options [record_proofs=1, document = pdf, document_output = "output", 
           document_variants = "document:outline=/proof,/ML"]
  theories All
  document_files "root.tex" "root.bib"
