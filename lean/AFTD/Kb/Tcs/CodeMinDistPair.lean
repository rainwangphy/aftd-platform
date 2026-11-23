import AFTD.Prelude
import AFTD.Kb.Tcs.CodeMinDist

/-!
# code_min_dist_pair

Topic: information   Node: ea0a0d9b0e8a

Provenance: helper lemma. folklore

Given implicit parameters n and q, for any two words x, y : Fin n → Fin q with x ≠ y, the two-element code {x, y} : Finset (Fin n → Fin q) satisfies code_min_dist {x, y} (hammingDist x y).
-/

/-- A two-element code {x, y} with x ≠ y has minimum distance equal to the Hamming distance between x and y. -/
lemma code_min_dist_pair {n q : ℕ} (x y : Fin n → Fin q) (hne : x ≠ y) :
    code_min_dist {x, y} (hammingDist x y) := by
  dsimp [code_min_dist]
  refine ⟨⟨x, by simp, y, by simp, hne, rfl⟩, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · subst ha hb; contradiction
  · subst ha hb; exact le_rfl
  · subst ha hb; rw [hammingDist_comm]
  · subst ha hb; contradiction
