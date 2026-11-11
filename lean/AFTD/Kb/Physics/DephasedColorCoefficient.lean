import AFTD.Prelude

/-!
# dephased_color_coefficient

Topic: quantum_mechanics   Node: d9dc3e79f0df

Provenance: helper lemma. Alternating-path interval expansion of the OP-827 block polynomial, checked in experiment 22445.

The tripartite inclusion-exclusion coefficient for an event requiring all colors in I and excluding all colors in O, with color 3 outside the three parties.
-/

def dephased_color_coefficient (I O : Finset (Fin 4)) : ℤ := open scoped Classical BigOperators in ∑ M ∈ ({0,1,2} : Finset (Fin 4)).powerset, if M.Nonempty ∧ I ⊆ M ∧ Disjoint O M then (if M.card % 2 = 1 then 1 else -1) else 0
