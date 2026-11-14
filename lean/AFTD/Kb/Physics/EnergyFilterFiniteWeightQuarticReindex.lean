import AFTD.Prelude

/-!
# energy_filter_finite_weight_quartic_reindex

Topic: statistical_mechanics   Node: 891b6fe29f71

Provenance: helper lemma. OP-892: exact finite-support trace reindexing.

For arbitrary real integer sequences a and b, if b is symmetric and vanishes outside a finite set, the four-index weighted cycle sum equals the triple quartic lattice sum weighted by the four-shift kernel.
-/

theorem energy_filter_finite_weight_quartic_reindex
    (a b : ℤ → ℝ) (s : Finset ℤ)
    (hs : ∀ t ∉ s, b t = 0) (hsym : ∀ t : ℤ, b (-t) = b t) :
    (∑' q : ℤ × ℤ × ℤ × ℤ,
      b q.1 * b q.2.1 * b q.2.2.1 * b q.2.2.2 *
        (a (-q.1-q.2.1) * a (-q.2.1-q.2.2.1) *
         a (-q.2.2.1-q.2.2.2) * a (-q.2.2.2-q.1))) =
    ∑' p : ℤ × ℤ × ℤ,
      (a p.1 * a p.2.1 * a p.2.2 * a (p.1-p.2.1+p.2.2)) *
      (∑' t : ℤ, b t * b (t+p.1) * b (t+p.2.1) * b (t+p.2.1-p.2.2)) := by
  classical
  let F : ℤ × ℤ × ℤ × ℤ → ℝ := fun q =>
    b q.1 * b q.2.1 * b q.2.2.1 * b q.2.2.2 *
      (a (-q.1-q.2.1) * a (-q.2.1-q.2.2.1) *
       a (-q.2.2.1-q.2.2.2) * a (-q.2.2.2-q.1))
  let H : (ℤ × ℤ × ℤ) × ℤ → ℝ := fun q =>
    (a q.1.1 * a q.1.2.1 * a q.1.2.2 * a (q.1.1-q.1.2.1+q.1.2.2)) *
    (b q.2 * b (q.2+q.1.1) * b (q.2+q.1.2.1) * b (q.2+q.1.2.1-q.1.2.2))
  have hF : Summable F := by
    apply summable_of_ne_finset_zero (s := s.product (s.product (s.product s)))
    intro q hq
    have hn : q.1 ∉ s ∨ q.2.1 ∉ s ∨ q.2.2.1 ∉ s ∨ q.2.2.2 ∉ s := by
      by_contra hn
      have h1 : q.1 ∈ s := by tauto
      have h2 : q.2.1 ∈ s := by tauto
      have h3 : q.2.2.1 ∈ s := by tauto
      have h4 : q.2.2.2 ∈ s := by tauto
      apply hq
      exact Finset.mem_product.mpr ⟨h1, Finset.mem_product.mpr ⟨h2, Finset.mem_product.mpr ⟨h3,h4⟩⟩⟩
    rcases hn with h1 | h2 | h3 | h4
    · simp [F, hs _ h1]
    · simp [F, hs _ h2]
    · simp [F, hs _ h3]
    · simp [F, hs _ h4]
  let e : ((ℤ × ℤ × ℤ) × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) := {
    toFun := fun q => (-q.1.1-q.2, q.2, -q.1.2.1-q.2, q.2+q.1.2.1-q.1.2.2)
    invFun := fun q => ((-q.1-q.2.1, -q.2.1-q.2.2.1, -q.2.2.1-q.2.2.2), q.2.1)
    left_inv := by intro q; rcases q with ⟨⟨u,v,w⟩,t⟩; simp <;> omega
    right_inv := by intro q; rcases q with ⟨α,β,γ,δ⟩; simp <;> omega }
  have heq : ∀ q, F (e q) = H q := by
    intro q
    rcases q with ⟨⟨u,v,w⟩,t⟩
    dsimp [F,H,e]
    have h1 : -u-t = -(t+u) := by omega
    have h2 : -v-t = -(t+v) := by omega
    have h3 : -(-u-t)-t = u := by omega
    have h4 : -t-(-v-t) = v := by omega
    have h5 : -(-v-t)-(t+v-w) = w := by omega
    have h6 : -(t+v-w)-(-u-t) = u-v+w := by omega
    rw [h3,h4,h5,h6,h1,h2,hsym,hsym]
    ring
  have hH : Summable H := by
    have ht := (e.summable_iff).2 hF
    convert ht using 1
    funext q
    exact (heq q).symm
  have hsum : (∑' q, F q) = ∑' q, H q := by
    calc
      _ = ∑' q, F (e q) := (e.tsum_eq F).symm
      _ = ∑' q, H q := tsum_congr heq
  change (∑' q, F q) = _
  rw [hsum, hH.tsum_prod]
  apply tsum_congr
  intro p
  dsimp [H]
  rw [tsum_mul_left]
