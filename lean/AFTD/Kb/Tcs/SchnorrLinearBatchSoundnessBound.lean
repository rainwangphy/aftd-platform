import AFTD.Prelude
import AFTD.Kb.Tcs.SchnorrVerify
import AFTD.Kb.Tcs.SchnorrMemZpowersIffExistsZmod
import AFTD.Kb.Tcs.SchnorrZpowEqPowZmodVal

/-!
# schnorr_linear_batch_soundness_bound

Topic: cryptography   Node: 183aa5549aa6

Provenance: original. Related work: Bellare, Garay, and Ralf 1998, Fast Batch Verification of Signatures

Let G be a commutative group, q a prime, and g in G an element of order q. Let pk, a₁, a₂ in Subgroup.zpowers g. For any challenges c₁, c₂ in ZMod q and responses s₁, s₂ in ZMod q, if transcript 1 does not satisfy Schnorr.Verify g pk a₁ c₁ s₁, then the set of linear batching weights α in ZMod q for which g^((s₁ + α * s₂).val) = a₁ * a₂^(α.val) * pk^((c₁ + α * c₂).val) holds has cardinality at most 1.
-/

theorem schnorr_linear_batch_soundness_bound_pow_eq_pow_zmod_val
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (n : ℕ) :
    g ^ n = g ^ (n : ZMod q).val := by
  have : NeZero q := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h2 := schnorr_zpow_eq_pow_zmod_val g hg (n : ℤ)
  push_cast at h2
  rw [← zpow_natCast, h2]

theorem schnorr_linear_batch_soundness_bound_pow_pow_eq_pow_mul_zmod
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (x y : ZMod q) :
    (g ^ x.val) ^ y.val = g ^ (x * y).val := by
  have : NeZero q := ⟨Nat.Prime.ne_zero Fact.out⟩
  rw [← pow_mul, schnorr_linear_batch_soundness_bound_pow_eq_pow_zmod_val g hg (x.val * y.val)]
  congr 1
  push_cast
  simp

theorem schnorr_linear_batch_soundness_bound_pow_mul_pow_eq_pow_add_zmod
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (x y : ZMod q) :
    g ^ x.val * g ^ y.val = g ^ (x + y).val := by
  have : NeZero q := ⟨Nat.Prime.ne_zero Fact.out⟩
  rw [← pow_add, schnorr_linear_batch_soundness_bound_pow_eq_pow_zmod_val g hg (x.val + y.val)]
  congr 1
  push_cast
  simp

theorem schnorr_linear_batch_soundness_bound_g_pow_inj
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (k₁ k₂ : ZMod q) :
    g ^ k₁.val = g ^ k₂.val ↔ k₁ = k₂ := by
  have : NeZero q := ⟨Nat.Prime.ne_zero Fact.out⟩
  constructor
  · intro h
    rw [pow_eq_pow_iff_modEq, hg] at h
    have hs₁ := ZMod.val_lt k₁
    have hs₂ := ZMod.val_lt k₂
    change k₁.val % q = k₂.val % q at h
    rw [Nat.mod_eq_of_lt hs₁, Nat.mod_eq_of_lt hs₂] at h
    exact ZMod.val_injective q h
  · rintro rfl
    rfl

theorem schnorr_linear_batch_soundness_bound_verify_iff
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (r₁ w c₁ s₁ : ZMod q) :
    Schnorr.Verify g (g ^ w.val) (g ^ r₁.val) c₁ s₁ ↔ s₁ = r₁ + c₁ * w := by
  change g ^ s₁.val = g ^ r₁.val * (g ^ w.val) ^ c₁.val ↔ s₁ = r₁ + c₁ * w
  rw [schnorr_linear_batch_soundness_bound_pow_pow_eq_pow_mul_zmod g hg w c₁]
  rw [schnorr_linear_batch_soundness_bound_pow_mul_pow_eq_pow_add_zmod g hg r₁ (w * c₁)]
  have h_exp : r₁ + w * c₁ = r₁ + c₁ * w := by ring
  rw [h_exp]
  exact schnorr_linear_batch_soundness_bound_g_pow_inj g hg s₁ (r₁ + c₁ * w)

theorem schnorr_linear_batch_soundness_bound_batch_eq_iff
    {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (r₁ r₂ w c₁ c₂ s₁ s₂ α : ZMod q) :
    g ^ (s₁ + α * s₂).val = (g ^ r₁.val) * (g ^ r₂.val) ^ α.val * (g ^ w.val) ^ (c₁ + α * c₂).val ↔
    s₁ + α * s₂ = r₁ + c₁ * w + α * (r₂ + c₂ * w) := by
  have h_rhs : (g ^ r₁.val) * (g ^ r₂.val) ^ α.val * (g ^ w.val) ^ (c₁ + α * c₂).val =
      g ^ (r₁ + c₁ * w + α * (r₂ + c₂ * w)).val := by
    rw [schnorr_linear_batch_soundness_bound_pow_pow_eq_pow_mul_zmod g hg r₂ α]
    rw [schnorr_linear_batch_soundness_bound_pow_pow_eq_pow_mul_zmod g hg w (c₁ + α * c₂)]
    rw [schnorr_linear_batch_soundness_bound_pow_mul_pow_eq_pow_add_zmod g hg r₁ (r₂ * α)]
    rw [schnorr_linear_batch_soundness_bound_pow_mul_pow_eq_pow_add_zmod g hg (r₁ + r₂ * α) (w * (c₁ + α * c₂))]
    congr 2
    ring
  rw [h_rhs]
  exact schnorr_linear_batch_soundness_bound_g_pow_inj g hg (s₁ + α * s₂) (r₁ + c₁ * w + α * (r₂ + c₂ * w))

theorem schnorr_linear_batch_soundness_bound_linear_batch_eq_unique
    {R : Type*} [CommRing R] [IsDomain R]
    (r₁ r₂ w c₁ c₂ s₁ s₂ α₁ α₂ : R)
    (h₁ : s₁ + α₁ * s₂ = r₁ + c₁ * w + α₁ * (r₂ + c₂ * w))
    (h₂ : s₁ + α₂ * s₂ = r₁ + c₁ * w + α₂ * (r₂ + c₂ * w))
    (h_not : s₁ ≠ r₁ + c₁ * w) :
    α₁ = α₂ := by
  have h_diff : (α₁ - α₂) * (s₂ - (r₂ + c₂ * w)) = 0 := by
    calc (α₁ - α₂) * (s₂ - (r₂ + c₂ * w))
      _ = (s₁ + α₁ * s₂ - (r₁ + c₁ * w + α₁ * (r₂ + c₂ * w))) -
          (s₁ + α₂ * s₂ - (r₁ + c₁ * w + α₂ * (r₂ + c₂ * w))) := by ring
      _ = 0 - 0 := by rw [sub_eq_zero.mpr h₁, sub_eq_zero.mpr h₂]
      _ = 0 := sub_zero 0
  cases mul_eq_zero.mp h_diff with
  | inl h_sub => exact sub_eq_zero.mp h_sub
  | inr h_B =>
    have h_B_eq : s₂ = r₂ + c₂ * w := sub_eq_zero.mp h_B
    rw [h_B_eq] at h₁
    have h_contr : s₁ = r₁ + c₁ * w := by
      calc s₁ = (s₁ + α₁ * (r₂ + c₂ * w)) - α₁ * (r₂ + c₂ * w) := by ring
      _ = (r₁ + c₁ * w + α₁ * (r₂ + c₂ * w)) - α₁ * (r₂ + c₂ * w) := by rw [h₁]
      _ = r₁ + c₁ * w := by ring
    exact (h_not h_contr).elim

/-- Quantitative soundness bound for linear batch verification of Schnorr transcripts: at most one linear weight accepts an invalid transcript. -/
theorem schnorr_linear_batch_soundness_bound
    {G : Type*} [CommGroup G] [DecidableEq G] {q : ℕ} [Fact q.Prime] (g : G)
    (hg : orderOf g = q) (pk a₁ a₂ : G)
    (hpk : pk ∈ Subgroup.zpowers g)
    (ha₁ : a₁ ∈ Subgroup.zpowers g)
    (ha₂ : a₂ ∈ Subgroup.zpowers g)
    (c₁ c₂ s₁ s₂ : ZMod q)
    (hnot : ¬ Schnorr.Verify g pk a₁ c₁ s₁) :
    (Finset.filter (fun α : ZMod q =>
      g ^ (s₁ + α * s₂).val = a₁ * a₂ ^ α.val * pk ^ (c₁ + α * c₂).val) Finset.univ).card ≤ 1 := by
  obtain ⟨w, rfl⟩ := schnorr_mem_zpowers_iff_exists_zmod g hg pk hpk
  obtain ⟨r₁, rfl⟩ := schnorr_mem_zpowers_iff_exists_zmod g hg a₁ ha₁
  obtain ⟨r₂, rfl⟩ := schnorr_mem_zpowers_iff_exists_zmod g hg a₂ ha₂
  have hnot_alg : s₁ ≠ r₁ + c₁ * w := by
    intro h_eq
    apply hnot
    rwa [schnorr_linear_batch_soundness_bound_verify_iff g hg]
  rw [Finset.card_le_one_iff]
  intro α₁ α₂ hα₁ hα₂
  rw [Finset.mem_filter] at hα₁ hα₂
  rw [schnorr_linear_batch_soundness_bound_batch_eq_iff g hg] at hα₁ hα₂
  exact schnorr_linear_batch_soundness_bound_linear_batch_eq_unique r₁ r₂ w c₁ c₂ s₁ s₂ α₁ α₂ hα₁.2 hα₂.2 hnot_alg
