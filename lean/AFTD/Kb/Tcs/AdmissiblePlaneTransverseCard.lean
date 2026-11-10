import AFTD.Prelude
import AFTD.Kb.Tcs.AffineLine
import AFTD.Kb.Tcs.AffinePlane
import AFTD.Kb.Tcs.AdmissiblePlaneSet

/-!
# admissible_plane_transverse_card

Topic: combinatorics   Node: 79b90f3f7596

Provenance: helper lemma. arXiv:2611.12153 Lemma 2.1

Let p be a prime, S an admissible plane set in (ZMod p)^3, and suppose S contains the affine line through P in direction v ≠ 0. Then every affine plane transverse to v (meaning f(v) ≠ 0) meets S in exactly p points: (S ∩ affine_plane f c).ncard = p.
-/

private lemma admissible_plane_transverse_card_eq_const_of_le_of_sum_eq_card_mul
    {ι : Type*} [Fintype ι]
    {k : ℕ} {g : ι → ℕ} (hle : ∀ i, k ≤ g i)
    (hsum : ∑ i, g i = k * Fintype.card ι) : ∀ i, g i = k := by
  have hzero : ∑ i, (g i - k) = 0 := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => hle j), hsum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
    simp
  intro i
  have hi : g i - k = 0 :=
    (Finset.sum_eq_zero_iff (s := Finset.univ) (f := fun i => g i - k)).mp hzero i (Finset.mem_univ i)
  have : g i ≤ k := Nat.sub_eq_zero_iff_le.mp hi
  exact le_antisymm this (hle i)

/-- If an admissible plane set contains an affine line in direction v, then every affine plane transverse to v meets S in exactly p points. -/
theorem admissible_plane_transverse_card
    (p : ℕ) [Fact p.Prime] (S : Set (Fin 3 → ZMod p)) (hS : admissible_plane_set p S)
    (P v : Fin 3 → ZMod p) (hv : v ≠ 0) (hline : affine_line P v ⊆ S)
    (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p) (hf : f v ≠ 0) (c : ZMod p) :
    (S ∩ affine_plane f c).ncard = p := by
  obtain ⟨hScard, hSdiv⟩ := hS
  have hf0 : f ≠ 0 := by intro h; apply hf; simp [h]
  have hne : ∀ c, (S ∩ affine_plane f c).Nonempty := by
    intro c
    obtain ⟨t, ht⟩ : ∃ t : ZMod p, f (P + t • v) = c := by
      refine ⟨(c - f P) / f v, ?_⟩
      rw [map_add, map_smul, smul_eq_mul]
      field_simp
      ring
    exact ⟨P + t • v, hline ⟨t, rfl⟩, ht⟩
  have hle : ∀ c, p ≤ (S ∩ affine_plane f c).ncard := by
    intro c
    have hd : p ∣ (S ∩ affine_plane f c).ncard := hSdiv f hf0 c
    have hpos : 0 < (S ∩ affine_plane f c).ncard := (hne c).ncard_pos
    exact Nat.le_of_dvd hpos hd
  have hdisj : Pairwise (Function.onFun Disjoint (fun c => S ∩ affine_plane f c)) := by
    intro c c' hcc'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_inter_iff, affine_plane, Set.mem_ofPred_eq] at hx hx'
    exact hcc' (hx.2.symm.trans hx'.2)
  have hunion : (⋃ c, S ∩ affine_plane f c) = S := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, affine_plane, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨c, hx, _⟩; exact hx
    · intro hx; exact ⟨f x, hx, rfl⟩
  have hsum : ∑ c : ZMod p, (S ∩ affine_plane f c).ncard = p ^ 2 := by
    have h1 : (⋃ c, S ∩ affine_plane f c).ncard = ∑ᶠ c : ZMod p, (S ∩ affine_plane f c).ncard :=
      Set.ncard_iUnion_of_finite (fun c => Set.toFinite _) hdisj
    rw [hunion, finsum_eq_sum_of_fintype, hScard] at h1
    exact h1.symm
  have hmain : ∀ c, (S ∩ affine_plane f c).ncard = p := by
    apply admissible_plane_transverse_card_eq_const_of_le_of_sum_eq_card_mul (k := p) hle
    rw [hsum, ZMod.card p, pow_two]
  exact hmain c
