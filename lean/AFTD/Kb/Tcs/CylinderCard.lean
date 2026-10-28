import AFTD.Prelude
import AFTD.Kb.Tcs.CylinderSet

/-!
# cylinder_card

Topic: combinatorics   Node: 22063e17a266

Provenance: helper lemma. arXiv:2610.34758 Lemma 2.3 proof

Let $p$ be a prime number, and let $W \subseteq (\mathbb{Z}/p\mathbb{Z})^d$ be an $m$-dimensional subspace over $\mathbb{Z}/p\mathbb{Z}$. Let $e \in (\mathbb{Z}/p\mathbb{Z})^d$ with $e \notin W$, and let $A \subseteq \mathbb{Z}/p\mathbb{Z}$. Then the cylinder set $E_A = \{w + a \cdot e : w \in W, a \in A\}$ has cardinality $|E_A| = p^m |A|$.
-/

/-- Cardinality of the cylinder set E_A is p^m * |A|. -/
theorem cylinder_card
    (d : ℕ) (p : ℕ) [Fact p.Prime] (m : ℕ)
    (W : Submodule (ZMod p) (Fin d → ZMod p)) (e : Fin d → ZMod p)
    (h_dim : Module.finrank (ZMod p) W = m)
    (he : e ∉ W) (A : Set (ZMod p)) :
    (cylinder_set d W e A).ncard = p ^ m * A.ncard := by
  have h_img : cylinder_set d W e A =
      (fun p : (Fin d → ZMod p) × ZMod p => p.1 + p.2 • e) '' ((W : Set (Fin d → ZMod p)) ×ˢ A) := by
    ext x
    simp only [cylinder_set, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨w, hw, a, ha, rfl⟩
      exact ⟨w, a, ⟨hw, ha⟩, rfl⟩
    · rintro ⟨w, a, ⟨hw, ha⟩, rfl⟩
      exact ⟨w, hw, a, ha, rfl⟩
  have h_inj : Set.InjOn (fun p : (Fin d → ZMod p) × ZMod p => p.1 + p.2 • e)
      ((W : Set (Fin d → ZMod p)) ×ˢ A) := by
    intro ⟨w1, a1⟩ hw1 ⟨w2, a2⟩ hw2 h
    dsimp at h
    have hw1' : w1 ∈ W := hw1.1
    have hw2' : w2 ∈ W := hw2.1
    have h_eq : (a1 - a2) • e = w2 - w1 := by
      rw [sub_smul]
      calc
        a1 • e - a2 • e = (w1 + a1 • e) - w1 - a2 • e := by abel
        _ = (w2 + a2 • e) - w1 - a2 • e := by rw [h]
        _ = w2 - w1 := by abel
    by_cases ha : a1 = a2
    · subst ha
      have : w1 = w2 := by simpa using h
      simp [this]
    · have h_inv : (a1 - a2) ≠ 0 := sub_ne_zero.mpr ha
      have h_e : e = (a1 - a2)⁻¹ • (w2 - w1) := by
        rw [← h_eq, smul_smul, inv_mul_cancel₀ h_inv, one_smul]
      have heW : e ∈ W := by
        rw [h_e]
        exact W.smul_mem _ (W.sub_mem hw2' hw1')
      exact (he heW).elim
  have h_card_W : (W : Set (Fin d → ZMod p)).ncard = p ^ m := by
    classical
    have : Fintype W := Subtype.fintype _
    change Nat.card W = _
    rw [Nat.card_eq_fintype_card, @Module.card_eq_pow_finrank (ZMod p) W, ZMod.card, h_dim]
  rw [h_img, h_inj.ncard_image, Set.ncard_prod, h_card_W]
