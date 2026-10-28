import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad
import AFTD.Kb.Tcs.IsTotallyIsotropic

/-!
# cylinder_quad_expansion

Topic: combinatorics   Node: 43a72df19226

Provenance: helper lemma. arXiv:2610.34758 Lemma 2.3 proof

For any natural numbers $d$ and $p$, any submodule $W \le (\mathbb{Z}/p\mathbb{Z})^d$ that is totally isotropic with respect to $Q_d$, and any vector $e \in (\mathbb{Z}/p\mathbb{Z})^d$ orthogonal to every element of $W$ under the standard dot product, for all $w, w' \in W$ and all $a, b \in \mathbb{Z}/p\mathbb{Z}$, $Q_d((w + a \cdot e) - (w' + b \cdot e)) = (a - b)^2 Q_d(e)$.
-/

lemma cylinder_quad_expansion_eq_dotProduct (d : ℕ) {p : ℕ} (x : Fin d → ZMod p) :
    standard_quad d x = dotProduct x x := by
  simp [standard_quad, dotProduct, sq]

/-- Expansion of the standard quadratic form on differences of elements of the cylinder set. -/
theorem cylinder_quad_expansion
    (d : ℕ) {p : ℕ}
    (W : Submodule (ZMod p) (Fin d → ZMod p)) (e : Fin d → ZMod p)
    (h_iso : is_totally_isotropic d W)
    (h_orth : ∀ w ∈ W, dotProduct e w = 0) :
    ∀ w ∈ W, ∀ w' ∈ W, ∀ (a b : ZMod p),
      standard_quad d ((w + a • e) - (w' + b • e)) = (a - b) ^ 2 * standard_quad d e := by
  intro w hw w' hw' a b
  have h_diff : (w + a • e) - (w' + b • e) = (w - w') + (a - b) • e := by module
  rw [h_diff]
  rw [cylinder_quad_expansion_eq_dotProduct]
  have hu_mem : w - w' ∈ W := W.sub_mem hw hw'
  have heu : dotProduct e (w - w') = 0 := h_orth (w - w') hu_mem
  have hue : dotProduct (w - w') e = 0 := by rw [dotProduct_comm, heu]
  have huu : dotProduct (w - w') (w - w') = 0 := by
    rw [← cylinder_quad_expansion_eq_dotProduct]
    exact h_iso (w - w') hu_mem
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  rw [huu, heu, hue]
  rw [← cylinder_quad_expansion_eq_dotProduct]
  ring
