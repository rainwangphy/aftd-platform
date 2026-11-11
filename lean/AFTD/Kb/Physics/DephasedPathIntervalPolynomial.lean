import AFTD.Prelude
import AFTD.Kb.Physics.DephasedColorCoefficient
import AFTD.Kb.Physics.DephasedPathIntervalBlock

/-!
# dephased_path_interval_polynomial

Topic: quantum_mechanics   Node: 9f35f4bee2bf

Provenance: helper lemma. Alternating-interval formula checked against supported-kernel enumeration for 65,000 path-and-leaf colorings in experiment 22445.

The explicit interval expansion of the block-polynomial tripartite gap on an active path; left and right record the colors of fully dephased leaves at its endpoints.
-/

noncomputable def dephased_path_interval_polynomial (n : ℕ) (color : Fin n → Fin 4) (left right : Finset (Fin 4)) (q : Fin n → ℝ) : ℝ := open scoped Classical BigOperators in ∑ i : Fin n, ∑ j : Fin n, if i.val ≤ j.val ∧ i.val % 2 = j.val % 2 then let X := dephased_path_interval_block n i j; let boundary := (Finset.univ.filter fun k : Fin n => k.val + 1 = i.val ∨ j.val + 1 = k.val).image color; let inside := X.image color ∪ boundary ∪ (if i.val = 0 then left else ∅) ∪ (if j.val + 1 = n then right else ∅); let outside := (Finset.univ.filter fun k : Fin n => i.val < k.val ∧ k.val < j.val ∧ k.val % 2 ≠ i.val % 2).image color; (dephased_color_coefficient inside outside : ℝ) * ∏ k ∈ X, q k else 0
