
JEDIT_SESSION=Lots-Of-Stuff
ISABELLE_DIR=/opt/Isabelle2021
ISABELLE=$(ISABELLE_DIR)/bin/isabelle
NAME=Complex_Bounded_Operators

edit :
	"$(ISABELLE)" jedit -l "$(SESSION)" -d . All.thy &

EXTRA_THYS=General Operator_Norm Vector_Spaces Infinite_Set_Sum Ordered_Fields Jordan_Normal_Form Lattice Pretty_Code_Examples
THYS=Complex_Vector_Spaces0 Complex_Vector_Spaces Complex_Inner_Product0 Complex_Inner_Product Complex_Euclidean_Space0 Complex_Bounded_Linear_Function0 Complex_Bounded_Linear_Function One_Dimensional_Spaces Complex_L2 Cblinfun_Matrix Cblinfun_Code Cblinfun_Code_Examples

bounded-operators-afp.zip : ROOT.AFP document/root.tex document/root.bib LICENSE README.md $(THYS:%=%.thy) $(EXTRA_THYS:%=extra/Extra_%.thy)
	rm -rf tmp $@
	mkdir -p tmp/$(NAME)
	cp --parents $^ tmp/$(NAME)
	mv tmp/$(NAME)/ROOT.AFP tmp/$(NAME)/ROOT
	cd tmp/$(NAME) && sed -i -e "s/$(NAME)-Extra/$(NAME)/g" *.thy
	cd tmp && zip -r $@ $(NAME)
	mv tmp/$@ .

test-afp : bounded-operators-afp.zip
	rm -rf tmp
	mkdir -p tmp
	cd tmp && unzip ../$^
	cd tmp/$(NAME) && "$(ISABELLE)" build -b -d . -v $(NAME)
