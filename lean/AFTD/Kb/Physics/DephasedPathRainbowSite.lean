import AFTD.Prelude

/-!
# dephased_path_rainbow_site

Topic: quantum_mechanics   Node: 2bcb6f1f43d9

Provenance: helper lemma. Reduced path finite-state certificate in experiment 22652.

An internal path site whose two neighbors and itself carry the three different party colors.
-/

def dephased_path_rainbow_site (n : ℕ) (color : Fin n → Fin 4) (j : Fin n) : Prop := ∃ l r : Fin n, l.val + 1 = j.val ∧ j.val + 1 = r.val ∧ ({color l, color j, color r} : Finset (Fin 4)) = {0,1,2}
