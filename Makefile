FILES = All.thy Banach_Steinhaus/ROOT					\
        Banach_Steinhaus/Banach_Steinhaus.thy ROOT ROOTS		\
        Banach_Steinhaus/Banach_Steinhaus_Missing.thy			\
        Banach_Steinhaus/document/root.tex				\
        Banach_Steinhaus/document/root.bib Preliminaries.thy		\
        Bounded_Operators.thy Complex_Vector_Spaces.thy			\
        Complex_Inner_Product.thy Complex_L2.thy			\
        Bounded_Operators_Code.thy Bounded_Operators_Matrices.thy	\
        Bounded_Operators_Code_Examples.thy				\
        Jordan_Normal_Form_Missing.thy document/root.tex


bounded-operators-cpp.zip : $(FILES)
	rm -rf tmp
	mkdir -p tmp/Banach_Steinhaus/document
	mkdir -p tmp/document
	set -e; for i in $^; do cp "$$i" tmp/"$$i"; done
	for i in tmp/*.thy tmp/document/*.tex tmp/Banach_Steinhaus/*.thy tmp/Banach_Steinhaus/document/*.tex; do \
		sed -i -e 's/Dominique Unruh, University of Tartu, unruh@ut.ee/Anonymous/g' \
		-e 's/Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee/Anonymous/g' \
		-e 's/Dominique Unruh, University of Tartu/Anonymous/g' \
		-e 's/Dominique Unruh/Anonymous/g' \
		-e "s/Jos..e Manuel Rodr..iguez Caballero/Anonymous/g" \
		-e "s/Jose Manuel Rodriguez Caballero/Anonymous/g" \
		-e "s/José/Anonymous/g" \
		-e "s/Jose/Anonymous/g" \
		-e "s/Dominique/Anonymous/g" \
		"$$i"; \
	done
	if grep -ri unruh tmp; then false; fi
	if grep -ri caballero tmp; then false; fi
	if grep -ri josé tmp; then false; fi
	if grep -ri manuel tmp; then false; fi
	if grep -ri iguez tmp; then false; fi
	if grep -ri jose tmp; then false; fi
	if grep -ri dominique tmp; then false; fi
	rm -f bounded-operators-cpp.zip
	cd tmp && zip -r ../$@ *
	rm -rf tmp

	rm -rf tmp2
	mkdir tmp2
	cd tmp2 && unzip ../$@
	rm -f /opt/Isabelle2019/heaps/polyml-5.8_x86_64_32-linux/Bounded_Operators
	cd tmp2 && /opt/Isabelle2019/bin/isabelle build -d . Bounded_Operators
	rm -rf tmp2
