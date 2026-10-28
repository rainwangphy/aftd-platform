import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad
import AFTD.Kb.Tcs.IsTotallyIsotropic
import AFTD.Kb.Tcs.DistanceSet
import AFTD.Kb.Tcs.CylinderSet
import AFTD.Kb.Tcs.DiffSqScaled
import AFTD.Kb.Tcs.CylinderQuadExpansion

/-!
# cylinder_distance_set

Topic: combinatorics   Node: 1ed2df789ab6

Provenance: helper lemma. arXiv:2610.34758 Lemma 2.3 proof

For any natural numbers $d$ and $p$, any submodule $W \le (\mathbb{Z}/p\mathbb{Z})^d$ that is totally isotropic with respect to $Q_d$, any vector $e \in (\mathbb{Z}/p\mathbb{Z})^d$ orthogonal to every element of $W$ under the standard dot product, and any subset $A \subset \mathbb{Z}/p\mathbb{Z}$, the distance set $\Delta(E_A)$ of the cylinder set $E_A = \{w + a \cdot e : w \in W, a \in A\}$ equals the scaled squared difference set $Q_d(e) (A - A)^2$.
-/

/-- Distance set of the cylinder set E_A equals the scaled squared difference set kappa * (A - A)^2. -/
theorem cylinder_distance_set
    (d : ℕ) {p : ℕ}
    (W : Submodule (ZMod p) (Fin d → ZMod p)) (e : Fin d → ZMod p)
    (h_iso : is_totally_isotropic d W)
    (h_orth : ∀ w ∈ W, dotProduct e w = 0)
    (A : Set (ZMod p)) :
    distance_set d (cylinder_set d W e A) = diff_sq_scaled (standard_quad d e) A := by
  ext x
  simp only [distance_set, cylinder_set, diff_sq_scaled]
  constructor
  · rintro ⟨u, ⟨w1, hw1, a, ha, rfl⟩, v, ⟨w2, hw2, b, hb, rfl⟩, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [cylinder_quad_expansion d W e h_iso h_orth w1 hw1 w2 hw2 a b]
    ring
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨0 + a • e, ⟨0, W.zero_mem, a, ha, rfl⟩, 0 + b • e, ⟨0, W.zero_mem, b, hb, rfl⟩, ?_⟩
    rw [cylinder_quad_expansion d W e h_iso h_orth 0 W.zero_mem 0 W.zero_mem a b]
    ring
