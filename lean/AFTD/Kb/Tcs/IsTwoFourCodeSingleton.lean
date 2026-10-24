import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoFourCode

/-!
# is_two_four_code_singleton

Topic: information   Node: 49f8811a6483

Provenance: helper lemma. folklore

Any singleton set $\{x\} \subseteq (\mathrm{Fin}\, n \to \mathrm{Fin}\, q)$ is a $\{2, 4\}$-code.
-/

/-- Any singleton code is vacuously a {2,4}-code. -/
theorem is_two_four_code_singleton (n q : ℕ) (x : Fin n → Fin q) : is_two_four_code ({x} : Set (Fin n → Fin q)) := by
  intro y hy z hz hyz
  rw [Set.mem_singleton_iff] at hy hz
  subst hy hz
  exact (hyz rfl).elim
