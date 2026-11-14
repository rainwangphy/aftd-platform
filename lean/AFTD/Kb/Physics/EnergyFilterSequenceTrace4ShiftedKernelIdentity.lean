import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_sequence_trace4_shifted_kernel_identity

Topic: statistical_mechanics   Node: 637a8fa21442

Provenance: helper lemma. OP-892: exact shifted-kernel reindexing, tested in experiment 26270.

For every real integer sequence a and natural k, the fourfold binomial trace numerator divided by the fourth power of the central binomial coefficient equals the triple sum of a(u)a(v)a(w)a(u−v+w) times the centered-binomial quartic kernel at shifts u, v and v−w, with the integer weight zero outside its valid range.
-/

private lemma eft4_bzero (k : ℕ) (s : ℤ)
    (h : s ∉ Finset.Icc (-(k:ℤ)) (k:ℤ)) : energy_filter_centered_binomial_weight k s = 0 := by
  unfold energy_filter_centered_binomial_weight
  simp only [Finset.mem_Icc] at h
  rw [if_neg (by omega)]

private lemma eft4_beven (k : ℕ) (s : ℤ) :
    energy_filter_centered_binomial_weight k (-s) = energy_filter_centered_binomial_weight k s := by
  by_cases h : -(k:ℤ) ≤ s ∧ s ≤ (k:ℤ)
  · have h' : -(k:ℤ) ≤ -s ∧ -s ≤ (k:ℤ) := ⟨by omega, by omega⟩
    simp only [energy_filter_centered_binomial_weight, if_pos h, if_pos h']
    have hj : ((k:ℤ) + s).toNat ≤ 2*k := by omega
    have hcast : ((k:ℤ) + -s).toNat = 2*k - ((k:ℤ) + s).toNat := by omega
    rw [hcast, Nat.choose_symm hj]
  · have h' : ¬(-(k:ℤ) ≤ -s ∧ -s ≤ (k:ℤ)) := by omega
    simp only [energy_filter_centered_binomial_weight, if_neg h, if_neg h']

private lemma eft4_bnum (k : ℕ) (p : ℕ) (hp : p < 2*k+1) :
    energy_filter_centered_binomial_weight k ((p:ℤ) - (k:ℤ))
      = (Nat.choose (2*k) p : ℝ) / (Nat.choose (2*k) k : ℝ) := by
  have hp' : p ≤ 2*k := by omega
  have h1 : -((k:ℤ)) ≤ (p:ℤ) - (k:ℤ) := by
    have : (0:ℤ) ≤ (p:ℤ) := by exact_mod_cast Nat.zero_le p
    omega
  have h2 : (p:ℤ) - (k:ℤ) ≤ (k:ℤ) := by
    have : (p:ℤ) ≤ 2*(k:ℤ) := by exact_mod_cast hp'
    omega
  rw [energy_filter_centered_binomial_weight, if_pos ⟨h1, h2⟩]
  have hidx : ((k:ℤ) + ((p:ℤ) - (k:ℤ))).toNat = p := by
    have : (k:ℤ) + ((p:ℤ) - (k:ℤ)) = (p:ℤ) := by ring
    rw [this]; simp
  rw [hidx]

private lemma eft4_randshift (k : ℕ) (f : ℤ → ℝ) :
    (∑ p ∈ Finset.range (2 * k + 1), f ((p:ℤ) - (k:ℤ))) = ∑ s ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), f s := by
  refine Finset.sum_nbij' (fun p : ℕ => (p:ℤ) - (k:ℤ)) (fun s : ℤ => (s + (k:ℤ)).toNat) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_range] at hp
    simp only [Finset.mem_Icc]
    have hp' : (p:ℤ) < 2*(k:ℤ) + 1 := by exact_mod_cast hp
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    have h1 : (0:ℤ) ≤ s + (k:ℤ) := by omega
    have h2 : s + (k:ℤ) ≤ 2*(k:ℤ) := by omega
    have h3 : ((s + (k:ℤ)).toNat : ℤ) = s + (k:ℤ) := Int.toNat_of_nonneg h1
    omega
  · intro p hp
    simp only [Finset.mem_range] at hp
    show (((p:ℤ) - (k:ℤ)) + (k:ℤ)).toNat = p
    have : ((p:ℤ) - (k:ℤ)) + (k:ℤ) = (p:ℤ) := by ring
    rw [this]; simp
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    show ((s + (k:ℤ)).toNat : ℤ) - (k:ℤ) = s
    rw [Int.toNat_of_nonneg (show (0:ℤ) ≤ s + (k:ℤ) by omega)]
    ring
  · intro p hp
    rfl

private lemma eft4_reindex4 (k : ℕ) (F : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ r ∈ Finset.range (2*k+1), ∑ t ∈ Finset.range (2*k+1),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) ((r:ℤ)-(k:ℤ)) ((t:ℤ)-(k:ℤ)))
    = ∑ α ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
      ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F α β γ δ := by
  have h1 : (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ r ∈ Finset.range (2*k+1), ∑ t ∈ Finset.range (2*k+1),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) ((r:ℤ)-(k:ℤ)) ((t:ℤ)-(k:ℤ)))
      = (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ r ∈ Finset.range (2*k+1), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) ((r:ℤ)-(k:ℤ)) δ) := by
    simp only [eft4_randshift]
  have h2 : (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ r ∈ Finset.range (2*k+1), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) ((r:ℤ)-(k:ℤ)) δ)
      = (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) γ δ) := by
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      eft4_randshift k (fun γ => ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) γ δ)))
  have h3 : (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
        F ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) γ δ)
      = (∑ p ∈ Finset.range (2*k+1),
      ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
      ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F ((p:ℤ)-(k:ℤ)) β γ δ) := by
    refine Finset.sum_congr rfl (fun p _ =>
      eft4_randshift k
        (fun β => ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F ((p:ℤ)-(k:ℤ)) β γ δ))
  have h4 : (∑ p ∈ Finset.range (2*k+1),
      ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
      ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F ((p:ℤ)-(k:ℤ)) β γ δ)
      = ∑ α ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
      ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F α β γ δ :=
    eft4_randshift k
      (fun α => ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
        ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), F α β γ δ)
  exact h1.trans (h2.trans (h3.trans h4))

private def eft4Equiv : (ℤ × ℤ × ℤ) × ℤ ≃ (ℤ × ℤ × ℤ × ℤ) where
  toFun z := (-(z.1.1) - z.2, z.2, -(z.1.2.1) - z.2, z.2 + z.1.2.1 - z.1.2.2)
  invFun y := ((- y.1 - y.2.1, - y.2.1 - y.2.2.1, - y.2.2.1 - y.2.2.2), y.2.1)
  left_inv := by
    rintro ⟨⟨u, v, w⟩, t⟩
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    all_goals first | ring | trivial
  right_inv := by
    rintro ⟨α, β, γ, δ⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first | ring | trivial

private noncomputable def eft4L (a : ℤ → ℝ) (k : ℕ) (α β γ δ : ℤ) : ℝ :=
  energy_filter_centered_binomial_weight k α * energy_filter_centered_binomial_weight k β *
    energy_filter_centered_binomial_weight k γ * energy_filter_centered_binomial_weight k δ *
    (a (-α - β) * a (-β - γ) * a (-γ - δ) * a (-δ - α))

private noncomputable def eft4G (a : ℤ → ℝ) (k : ℕ) (y : ℤ × ℤ × ℤ × ℤ) : ℝ :=
  eft4L a k y.1 y.2.1 y.2.2.1 y.2.2.2

private noncomputable def eft4A (a : ℤ → ℝ) (x : ℤ × ℤ × ℤ) : ℝ :=
  a x.1 * a x.2.1 * a x.2.2 * a (x.1 - x.2.1 + x.2.2)

private noncomputable def eft4P (k : ℕ) (x : ℤ × ℤ × ℤ) (t : ℤ) : ℝ :=
  energy_filter_centered_binomial_weight k t * energy_filter_centered_binomial_weight k (t + x.1) *
    energy_filter_centered_binomial_weight k (t + x.2.1) *
    energy_filter_centered_binomial_weight k (t + x.2.1 - x.2.2)

private noncomputable def eft4W (a : ℤ → ℝ) (k : ℕ) (z : (ℤ × ℤ × ℤ) × ℤ) : ℝ :=
  eft4A a z.1 * eft4P k z.1 z.2

private noncomputable def eft4S (a : ℤ → ℝ) (k : ℕ) : ℝ :=
  ∑ α ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
    ∑ γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), ∑ δ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), eft4L a k α β γ δ

private noncomputable def eft4R (a : ℤ → ℝ) (k : ℕ) : ℝ :=
  ∑' x : ℤ × ℤ × ℤ, eft4A a x * (∑' t : ℤ, eft4P k x t)

private noncomputable def eft4T (a : ℤ → ℝ) (k : ℕ) (p q r s : ℕ) : ℝ :=
  (Nat.choose (2*k) p : ℝ) * (Nat.choose (2*k) q : ℝ) * (Nat.choose (2*k) r : ℝ) *
    (Nat.choose (2*k) s : ℝ) *
    (a (2 * (k:ℤ) - (p:ℤ) - (q:ℤ)) * a (2 * (k:ℤ) - (q:ℤ) - (r:ℤ)) *
     a (2 * (k:ℤ) - (r:ℤ) - (s:ℤ)) * a (2 * (k:ℤ) - (s:ℤ) - (p:ℤ)))

private noncomputable def eft4LH (a : ℤ → ℝ) (k : ℕ) : ℝ :=
  (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
    ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1), eft4T a k p q r s) /
    (Nat.choose (2 * k) k : ℝ) ^ 4

private lemma eft4_Weq (a : ℤ → ℝ) (k : ℕ) (u v w t : ℤ) :
    eft4W a k ((u, v, w), t) = eft4G a k (eft4Equiv ((u, v, w), t)) := by
  have h1 : eft4Equiv ((u, v, w), t) = ((-u - t, t, -v - t, t + v - w) : ℤ × ℤ × ℤ × ℤ) := rfl
  rw [h1]
  simp only [eft4G, eft4L, eft4W, eft4A, eft4P]
  rw [show -(-u - t) - t = u by ring, show -t - (-v - t) = v by ring,
      show -(-v - t) - (t + v - w) = w by ring, show -(t + v - w) - (-u - t) = u - v + w by ring]
  rw [show -u - t = -(u + t) by ring, eft4_beven, show -v - t = -(v + t) by ring, eft4_beven]
  rw [add_comm u t, add_comm v t]
  ring

private lemma eft4G_zero (a : ℤ → ℝ) (k : ℕ) :
    ∀ y ∉ Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ (Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ
      (Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ Finset.Icc (-(k:ℤ)) (k:ℤ))), eft4G a k y = 0 := by
  rintro ⟨α, β, γ, δ⟩ hy
  simp only [Finset.mem_product] at hy
  by_cases hα : α ∈ Finset.Icc (-(k:ℤ)) (k:ℤ)
  · by_cases hβ : β ∈ Finset.Icc (-(k:ℤ)) (k:ℤ)
    · by_cases hγ : γ ∈ Finset.Icc (-(k:ℤ)) (k:ℤ)
      · have hδ : δ ∉ Finset.Icc (-(k:ℤ)) (k:ℤ) := by tauto
        simp only [eft4G, eft4L, eft4_bzero k δ hδ]; ring
      · simp only [eft4G, eft4L, eft4_bzero k γ hγ]; ring
    · simp only [eft4G, eft4L, eft4_bzero k β hβ]; ring
  · simp only [eft4G, eft4L, eft4_bzero k α hα]; ring

private lemma eft4_summable (a : ℤ → ℝ) (k : ℕ) : Summable (eft4G a k) :=
  summable_of_ne_finset_zero (eft4G_zero a k)

private lemma eft4_summable_W (a : ℤ → ℝ) (k : ℕ) : Summable (eft4W a k) := by
  have h : Summable (fun z : (ℤ × ℤ × ℤ) × ℤ => eft4G a k (eft4Equiv z)) :=
    (Equiv.summable_iff eft4Equiv).mpr (eft4_summable a k)
  refine h.congr ?_
  rintro ⟨⟨u, v, w⟩, t⟩
  exact (eft4_Weq a k u v w t).symm

private lemma eft4_rhs (a : ℤ → ℝ) (k : ℕ) : eft4R a k = eft4S a k := by
  have hsum : Summable (eft4W a k) := eft4_summable_W a k
  have hbox := eft4G_zero a k
  calc eft4R a k
      = ∑' x : ℤ × ℤ × ℤ, ∑' t : ℤ, eft4A a x * eft4P k x t := by
          simp only [eft4R]
          exact tsum_congr (fun x => by rw [tsum_mul_left])
    _ = ∑' z : (ℤ × ℤ × ℤ) × ℤ, eft4W a k z := (Summable.tsum_prod hsum).symm
    _ = ∑' y : ℤ × ℤ × ℤ × ℤ, eft4G a k y := by
          refine Eq.trans (tsum_congr ?_) (Equiv.tsum_eq eft4Equiv (eft4G a k))
          rintro ⟨⟨u, v, w⟩, t⟩
          exact eft4_Weq a k u v w t
    _ = ∑ y ∈ Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ (Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ
          (Finset.Icc (-(k:ℤ)) (k:ℤ) ×ˢ Finset.Icc (-(k:ℤ)) (k:ℤ))), eft4G a k y := tsum_eq_sum hbox
    _ = eft4S a k := by
          simp only [eft4S, Finset.sum_product, eft4G]

private lemma eft4_term_eq (a : ℤ → ℝ) (k p q r s : ℕ) (hp : p < 2*k+1) (hq : q < 2*k+1)
    (hr : r < 2*k+1) (hs : s < 2*k+1) :
    eft4T a k p q r s / (Nat.choose (2 * k) k : ℝ) ^ 4 =
      eft4L a k ((p:ℤ) - (k:ℤ)) ((q:ℤ) - (k:ℤ)) ((r:ℤ) - (k:ℤ)) ((s:ℤ) - (k:ℤ)) := by
  have hCk : (Nat.choose (2*k) k : ℝ) ≠ 0 := by
    have : 0 < Nat.choose (2*k) k := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  simp only [eft4T, eft4L]
  rw [eft4_bnum k p hp, eft4_bnum k q hq, eft4_bnum k r hr, eft4_bnum k s hs]
  have e1 : 2 * (k : ℤ) - (p : ℤ) - (q : ℤ) = -((p:ℤ) - (k:ℤ)) - ((q:ℤ) - (k:ℤ)) := by ring
  have e2 : 2 * (k : ℤ) - (q : ℤ) - (r : ℤ) = -((q:ℤ) - (k:ℤ)) - ((r:ℤ) - (k:ℤ)) := by ring
  have e3 : 2 * (k : ℤ) - (r : ℤ) - (s : ℤ) = -((r:ℤ) - (k:ℤ)) - ((s:ℤ) - (k:ℤ)) := by ring
  have e4 : 2 * (k : ℤ) - (s : ℤ) - (p : ℤ) = -((s:ℤ) - (k:ℤ)) - ((p:ℤ) - (k:ℤ)) := by ring
  rw [e1, e2, e3, e4]
  field_simp

private lemma eft4_lhs (a : ℤ → ℝ) (k : ℕ) : eft4LH a k = eft4S a k := by
  have step1 : (∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
      ∑ r ∈ Finset.range (2*k+1), ∑ s ∈ Finset.range (2*k+1),
        eft4T a k p q r s / (Nat.choose (2*k) k : ℝ)^4) =
      ∑ p ∈ Finset.range (2*k+1), ∑ q ∈ Finset.range (2*k+1),
        ∑ r ∈ Finset.range (2*k+1), ∑ s ∈ Finset.range (2*k+1),
          eft4L a k ((p:ℤ)-(k:ℤ)) ((q:ℤ)-(k:ℤ)) ((r:ℤ)-(k:ℤ)) ((s:ℤ)-(k:ℤ)) := by
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq =>
      Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))))
    exact eft4_term_eq a k p q r s (Finset.mem_range.mp hp) (Finset.mem_range.mp hq)
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)
  simp only [eft4LH, Finset.sum_div]
  rw [step1]
  exact eft4_reindex4 k (fun α β γ δ => eft4L a k α β γ δ)

private lemma eft4_main (a : ℤ → ℝ) (k : ℕ) : eft4LH a k = eft4R a k :=
  (eft4_lhs a k).trans (eft4_rhs a k).symm

theorem energy_filter_sequence_trace4_shifted_kernel_identity (a : ℤ → ℝ) (k : ℕ) :
    (∑ p ∈ Finset.range (2 * k + 1), ∑ q ∈ Finset.range (2 * k + 1),
     ∑ r ∈ Finset.range (2 * k + 1), ∑ s ∈ Finset.range (2 * k + 1),
      (Nat.choose (2 * k) p : ℝ) * (Nat.choose (2 * k) q : ℝ) *
        (Nat.choose (2 * k) r : ℝ) * (Nat.choose (2 * k) s : ℝ) *
        (a (2 * (k : ℤ) - (p : ℤ) - (q : ℤ)) * a (2 * (k : ℤ) - (q : ℤ) - (r : ℤ)) *
         a (2 * (k : ℤ) - (r : ℤ) - (s : ℤ)) * a (2 * (k : ℤ) - (s : ℤ) - (p : ℤ)))) /
      (Nat.choose (2 * k) k : ℝ) ^ 4 =
    ∑' x : ℤ × ℤ × ℤ,
      (a x.1 * a x.2.1 * a x.2.2 * a (x.1 - x.2.1 + x.2.2)) *
      (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
        energy_filter_centered_binomial_weight k (t + x.1) *
        energy_filter_centered_binomial_weight k (t + x.2.1) *
        energy_filter_centered_binomial_weight k (t + x.2.1 - x.2.2)) := by
  have := eft4_main a k
  simpa only [eft4LH, eft4R, eft4T, eft4A, eft4P] using this
