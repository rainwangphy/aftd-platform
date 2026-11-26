import AFTD.Prelude

/-!
# qutrit_bosonic_pair_code

Topic: quantum   Node: 68e1a1cbbee5

Provenance: helper lemma. OP-2299; exact rational two-copy PPT bosonic extension, experiments 40204 and 40206.

The symmetric occupation index of an unordered pair of qutrit labels.
-/

def qutrit_bosonic_pair_code (a b : Fin 3) : Fin 6 := (!![(0 : Fin 6), 1, 2; 1, 3, 4; 2, 4, 5]) a b
