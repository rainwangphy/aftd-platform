import AFTD.Prelude
import AFTD.Kb.Tcs.OrientationPerfectMatchingSign

/-!
# orientation_perfect_matching_sign_two

Topic: combinatorics   Node: f391c81207a7

Provenance: helper lemma. arXiv:2611.00468 (The symbolic pfaffian method I), sanity check of the sign of a perfect matching

In the complete graph on Fin 2, the perfect matching consisting of its single edge, oriented from 0 to 1, has sign 1.
-/

theorem orientation_perfect_matching_sign_two :
    orientation_perfect_matching_sign (G := (⊤ : SimpleGraph (Fin 2)))
      ⟨fun u v => u = 0 ∧ v = 1⟩ (⊤ : (⊤ : SimpleGraph (Fin 2)).Subgraph) = 1 := by
  have hex : ∃ π : Equiv.Perm (Fin 2), ∀ (j : ℕ) (hj : 2 * j + 1 < 2),
      (⊤ : (⊤ : SimpleGraph (Fin 2)).Subgraph).Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩) ∧
      (⟨fun u v => u = 0 ∧ v = 1⟩ : Digraph (Fin 2)).Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩) := by
    refine ⟨1, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simp
  unfold orientation_perfect_matching_sign
  rw [dif_pos hex]
  have hspec := hex.choose_spec 0 (by norm_num)
  have h1 : hex.choose = 1 := by
    obtain ⟨_, h0, h1⟩ := hspec
    ext i
    fin_cases i
    · simpa using congrArg Fin.val h0
    · simpa using congrArg Fin.val h1
  rw [h1]; simp
