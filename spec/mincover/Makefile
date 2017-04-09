TLC_METADIR := .states
TEX_METADIR := .aux

tlapm:
	tlapm -v -C Optimization.tla

tlc:
	tlc2 -deadlock -metadir $(TLC_METADIR) CyclicCore.tla

stx:
	tla2sany CyclicCore.tla

clean:
	-rm -rf *.tlaps *.toolbox workspace .aux/*

print_theorems:
	ag "AXIOM|ASSUMPTION|PROPOSITION|LEMMA|THEOREM|COROLLARY" \
		FiniteSetFacts.tla \
		Optimization.tla \
		MinCover.tla \
		Lattices.tla \
		Orthotopes.tla \
		CyclicCore.tla \
		StrongReduction.tla
