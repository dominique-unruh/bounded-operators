
JEDIT_SESSION=Lots-Of-Stuff
ISABELLE_DIR=/opt/Isabelle2021
ISABELLE=$(ISABELLE_DIR)/bin/isabelle
NAME=Complex_Bounded_Operators

edit :
	"$(ISABELLE)" jedit -l "$(SESSION)" -d . All.thy &

EXTRA_THYS=General Operator_Norm Vector_Spaces Ordered_Fields Jordan_Normal_Form Lattice Pretty_Code_Examples # Infinite_Set_Sum
THYS=Complex_Vector_Spaces0 Complex_Vector_Spaces Complex_Inner_Product0 Complex_Inner_Product Complex_Euclidean_Space0 Complex_Bounded_Linear_Function0 Complex_Bounded_Linear_Function One_Dimensional_Spaces Complex_L2 Cblinfun_Matrix Cblinfun_Code Cblinfun_Code_Examples

AFP_DIR=/opt/afp-devel/thys/Complex_Bounded_Operators
copy-to-afp : ROOT.AFP document/root.tex document/root.bib LICENSE README.md $(THYS:%=%.thy) $(EXTRA_THYS:%=extra/Extra_%.thy)
	rm -rv $(AFP_DIR)/*
	cp --parents $^ $(AFP_DIR)
	mv $(AFP_DIR)/ROOT.AFP $(AFP_DIR)/ROOT
	cd $(AFP_DIR) && sed -i -e "s/$(NAME)-Extra/$(NAME)/g" *.thy
	~/r/isabelle/bin/isabelle build -B $(NAME)
