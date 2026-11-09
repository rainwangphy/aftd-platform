import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsScaledBivaluedChores
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BivaluedRoundingOddMmsArithmetic
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.BivaluedRoundingEvenMmsArithmetic
import AFTD.Kb.Tcs.G

/-!
# two_agent_common_bivalued_safe_partition

Topic: fair_division   Node: 054d361179ea

Provenance: formalization of a published result. Source: arXiv:2409.13680

For any ratio r with 1 ≤ r ≤ 2, any number of chores m, and any two-agent chore cost profile c satisfying is_scaled_bivalued_chores r c, there exists a subset S of chores such that for each agent i : Fin 2, both S and its complement Finset.univ \ S have additive cost at most ((r + 1) / 2) * chore_maximin_share 2 (c i).
-/

set_option maxHeartbeats 4000000 in
lemma two_agent_common_bivalued_safe_partition_counts
    (n00 n01 n10 n11 : ℕ) :
    ∃ a b c d : ℕ, a ≤ n00 ∧ b ≤ n01 ∧ c ≤ n10 ∧ d ≤ n11 ∧
      2 * (a + b + c + d) ≤ n00 + n01 + n10 + n11 + 1 ∧
      n00 + n01 + n10 + n11 ≤ 2 * (a + b + c + d) + 1 ∧
      2 * (c + d) ≤ n10 + n11 + 1 ∧ n10 + n11 ≤ 2 * (c + d) + 1 ∧
      2 * (b + d) ≤ n01 + n11 + 1 ∧ n01 + n11 ≤ 2 * (b + d) + 1 := by
  obtain ⟨u00, e00, he00, rfl⟩ : ∃ u e : ℕ, e ≤ 1 ∧ n00 = 2 * u + e :=
    ⟨n00 / 2, n00 % 2, by omega, by omega⟩
  obtain ⟨u01, e01, he01, rfl⟩ : ∃ u e : ℕ, e ≤ 1 ∧ n01 = 2 * u + e :=
    ⟨n01 / 2, n01 % 2, by omega, by omega⟩
  obtain ⟨u10, e10, he10, rfl⟩ : ∃ u e : ℕ, e ≤ 1 ∧ n10 = 2 * u + e :=
    ⟨n10 / 2, n10 % 2, by omega, by omega⟩
  obtain ⟨u11, e11, he11, rfl⟩ : ∃ u e : ℕ, e ≤ 1 ∧ n11 = 2 * u + e :=
    ⟨n11 / 2, n11 % 2, by omega, by omega⟩
  interval_cases e00 <;> interval_cases e01 <;> interval_cases e10 <;> interval_cases e11
  all_goals first
    | exact ⟨u00, u01, u10, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00 + 1, u01, u10, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00, u01 + 1, u10, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00, u01, u10 + 1, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00, u01, u10, u11 + 1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00 + 1, u01 + 1, u10, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00 + 1, u01, u10 + 1, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨u00, u01 + 1, u10 + 1, u11, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
lemma two_agent_common_bivalued_safe_partition_card_union_four {α : Type*} [DecidableEq α]
    {A B C D : Finset α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    (A ∪ B ∪ C ∪ D).card = A.card + B.card + C.card + D.card := by
  have hABD : Disjoint (A ∪ B) D := Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have h2 : Disjoint ((A ∪ B) ∪ C) D := Finset.disjoint_union_left.mpr ⟨hABD, hCD⟩
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint hABC,
    Finset.card_union_of_disjoint hAB]

set_option maxHeartbeats 8000000 in
lemma two_agent_common_bivalued_safe_partition_balance (m : ℕ) (H0 H1 : Finset (Fin m)) :
    ∃ S : Finset (Fin m),
      S.card ≤ (m + 1) / 2 ∧ (Finset.univ \ S).card ≤ (m + 1) / 2 ∧
      (S ∩ H0).card ≤ (H0.card + 1) / 2 ∧ (H0 \ S).card ≤ (H0.card + 1) / 2 ∧
      (S ∩ H1).card ≤ (H1.card + 1) / 2 ∧ (H1 \ S).card ≤ (H1.card + 1) / 2 := by
  classical
  obtain ⟨A, B, C, D, hAdef, hBdef, hCdef, hDdef, hpart, dAB, dAC, dAD, dBC, dBD, dCD,
    hH0, hH1⟩ :
    ∃ A B C D : Finset (Fin m), A = Finset.univ \ (H0 ∪ H1) ∧ B = H1 \ H0 ∧ C = H0 \ H1 ∧
      D = H0 ∩ H1 ∧ A ∪ B ∪ C ∪ D = Finset.univ ∧ Disjoint A B ∧ Disjoint A C ∧
      Disjoint A D ∧ Disjoint B C ∧ Disjoint B D ∧ Disjoint C D ∧ H0 = C ∪ D ∧ H1 = B ∪ D := by
    refine ⟨Finset.univ \ (H0 ∪ H1), H1 \ H0, H0 \ H1, H0 ∩ H1, rfl, rfl, rfl, rfl, ?_⟩
    have mA : ∀ x : Fin m, x ∈ (Finset.univ \ (H0 ∪ H1) : Finset (Fin m)) ↔ x ∉ H0 ∧ x ∉ H1 :=
      fun x => by simp
    have mB : ∀ x : Fin m, x ∈ (H1 \ H0 : Finset (Fin m)) ↔ x ∈ H1 ∧ x ∉ H0 := fun x => by simp
    have mC : ∀ x : Fin m, x ∈ (H0 \ H1 : Finset (Fin m)) ↔ x ∈ H0 ∧ x ∉ H1 := fun x => by simp
    have mD : ∀ x : Fin m, x ∈ (H0 ∩ H1 : Finset (Fin m)) ↔ x ∈ H0 ∧ x ∈ H1 := fun x => by simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext x
      have a := mA x; have b := mB x; have c := mC x; have d := mD x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mA x).1 hx; have h2 := (mB x).1 hy; tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mA x).1 hx; have h2 := (mC x).1 hy; tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mA x).1 hx; have h2 := (mD x).1 hy; tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mB x).1 hx; have h2 := (mC x).1 hy; tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mB x).1 hx; have h2 := (mD x).1 hy; tauto
    · rw [Finset.disjoint_left]; intro x hx hy
      have h1 := (mC x).1 hx; have h2 := (mD x).1 hy; tauto
    · ext x
      have c := mC x; have d := mD x
      simp only [Finset.mem_union]
      tauto
    · ext x
      have b := mB x; have d := mD x
      simp only [Finset.mem_union]
      tauto
  obtain ⟨a, b, c, d, ha, hb, hc, hd, e1, e2, e3, e4, e5, e6⟩ :=
    two_agent_common_bivalued_safe_partition_counts A.card B.card C.card D.card
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq ha
  obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hb
  obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq hc
  obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq hd
  have eA0 : ∀ x, x ∈ A' → x ∉ H0 := by
    intro x hx
    have h : x ∈ A := hA'sub hx
    rw [hAdef] at h
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, not_or, true_and] at h
    exact h.1
  have eA1 : ∀ x, x ∈ A' → x ∉ H1 := by
    intro x hx
    have h : x ∈ A := hA'sub hx
    rw [hAdef] at h
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, not_or, true_and] at h
    exact h.2
  have eB0 : ∀ x, x ∈ B' → x ∉ H0 := by
    intro x hx
    have h : x ∈ B := hB'sub hx
    rw [hBdef] at h
    simp only [Finset.mem_sdiff] at h
    exact h.2
  have eB1 : ∀ x, x ∈ B' → x ∈ H1 := by
    intro x hx
    have h : x ∈ B := hB'sub hx
    rw [hBdef] at h
    simp only [Finset.mem_sdiff] at h
    exact h.1
  have eC0 : ∀ x, x ∈ C' → x ∈ H0 := by
    intro x hx
    have h : x ∈ C := hC'sub hx
    rw [hCdef] at h
    simp only [Finset.mem_sdiff] at h
    exact h.1
  have eC1 : ∀ x, x ∈ C' → x ∉ H1 := by
    intro x hx
    have h : x ∈ C := hC'sub hx
    rw [hCdef] at h
    simp only [Finset.mem_sdiff] at h
    exact h.2
  have eD0 : ∀ x, x ∈ D' → x ∈ H0 := by
    intro x hx
    have h : x ∈ D := hD'sub hx
    rw [hDdef] at h
    simp only [Finset.mem_inter] at h
    exact h.1
  have eD1 : ∀ x, x ∈ D' → x ∈ H1 := by
    intro x hx
    have h : x ∈ D := hD'sub hx
    rw [hDdef] at h
    simp only [Finset.mem_inter] at h
    exact h.2
  have hS0 : (A' ∪ B' ∪ C' ∪ D') ∩ H0 = C' ∪ D' := by
    ext x
    have h1 : x ∈ A' → x ∉ H0 := eA0 x
    have h2 : x ∈ B' → x ∉ H0 := eB0 x
    have h3 : x ∈ C' → x ∈ H0 := eC0 x
    have h4 : x ∈ D' → x ∈ H0 := eD0 x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hS1 : (A' ∪ B' ∪ C' ∪ D') ∩ H1 = B' ∪ D' := by
    ext x
    have h1 : x ∈ A' → x ∉ H1 := eA1 x
    have h2 : x ∈ B' → x ∈ H1 := eB1 x
    have h3 : x ∈ C' → x ∉ H1 := eC1 x
    have h4 : x ∈ D' → x ∈ H1 := eD1 x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hS0card : ((A' ∪ B' ∪ C' ∪ D') ∩ H0).card = c + d := by
    rw [hS0, Finset.card_union_of_disjoint (dCD.mono hC'sub hD'sub), hC'card, hD'card]
  have hS1card : ((A' ∪ B' ∪ C' ∪ D') ∩ H1).card = b + d := by
    rw [hS1, Finset.card_union_of_disjoint (dBD.mono hB'sub hD'sub), hB'card, hD'card]
  have hH0sdiff : H0 \ (A' ∪ B' ∪ C' ∪ D') = (C \ C') ∪ (D \ D') := by
    ext x
    have hx0 : x ∈ H0 ↔ x ∈ C ∨ x ∈ D := by rw [hH0]; exact Finset.mem_union
    have f1 : x ∈ A' → x ∉ C := fun hx hc => Finset.disjoint_left.1 dAC (hA'sub hx) hc
    have f2 : x ∈ A' → x ∉ D := fun hx hd => Finset.disjoint_left.1 dAD (hA'sub hx) hd
    have f3 : x ∈ B' → x ∉ C := fun hx hc => Finset.disjoint_left.1 dBC (hB'sub hx) hc
    have f4 : x ∈ B' → x ∉ D := fun hx hd => Finset.disjoint_left.1 dBD (hB'sub hx) hd
    have f5 : x ∈ C → x ∉ D' := fun hc hd => (Finset.disjoint_left.1 dCD hc) (hD'sub hd)
    have f6 : x ∈ D → x ∉ C' := fun hd hc => (Finset.disjoint_left.1 dCD (hC'sub hc)) hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hH1sdiff : H1 \ (A' ∪ B' ∪ C' ∪ D') = (B \ B') ∪ (D \ D') := by
    ext x
    have hx0 : x ∈ H1 ↔ x ∈ B ∨ x ∈ D := by rw [hH1]; exact Finset.mem_union
    have f1 : x ∈ A' → x ∉ B := fun hx hb => Finset.disjoint_left.1 dAB (hA'sub hx) hb
    have f2 : x ∈ A' → x ∉ D := fun hx hd => Finset.disjoint_left.1 dAD (hA'sub hx) hd
    have f3 : x ∈ C' → x ∉ B := fun hx hb => (Finset.disjoint_left.1 dBC hb) (hC'sub hx)
    have f4 : x ∈ C' → x ∉ D := fun hx hd => Finset.disjoint_left.1 dCD (hC'sub hx) hd
    have f5 : x ∈ B → x ∉ D' := fun hb hd => (Finset.disjoint_left.1 dBD hb) (hD'sub hd)
    have f6 : x ∈ D → x ∉ B' := fun hd hb => (Finset.disjoint_left.1 dBD (hB'sub hb)) hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hH0sdiffcard : (H0 \ (A' ∪ B' ∪ C' ∪ D')).card = (C \ C').card + (D \ D').card := by
    rw [hH0sdiff, Finset.card_union_of_disjoint
      (Disjoint.mono (Finset.sdiff_subset : C \ C' ⊆ C) (Finset.sdiff_subset : D \ D' ⊆ D) dCD)]
  have hH1sdiffcard : (H1 \ (A' ∪ B' ∪ C' ∪ D')).card = (B \ B').card + (D \ D').card := by
    rw [hH1sdiff, Finset.card_union_of_disjoint
      (Disjoint.mono (Finset.sdiff_subset : B \ B' ⊆ B) (Finset.sdiff_subset : D \ D' ⊆ D) dBD)]
  have hdCC' : (C \ C').card + C'.card = C.card := Finset.card_sdiff_add_card_eq_card hC'sub
  have hdDD' : (D \ D').card + D'.card = D.card := Finset.card_sdiff_add_card_eq_card hD'sub
  have hdBB' : (B \ B').card + B'.card = B.card := Finset.card_sdiff_add_card_eq_card hB'sub
  have hScard : (A' ∪ B' ∪ C' ∪ D').card = a + b + c + d := by
    rw [two_agent_common_bivalued_safe_partition_card_union_four (dAB.mono hA'sub hB'sub)
      (dAC.mono hA'sub hC'sub) (dAD.mono hA'sub hD'sub) (dBC.mono hB'sub hC'sub)
      (dBD.mono hB'sub hD'sub) (dCD.mono hC'sub hD'sub), hA'card, hB'card, hC'card, hD'card]
  have hpartcard : A.card + B.card + C.card + D.card = m := by
    have h := congrArg Finset.card hpart
    rw [two_agent_common_bivalued_safe_partition_card_union_four dAB dAC dAD dBC dBD dCD] at h
    simpa using h
  have hH0card : H0.card = C.card + D.card := by
    rw [hH0, Finset.card_union_of_disjoint dCD]
  have hH1card : H1.card = B.card + D.card := by
    rw [hH1, Finset.card_union_of_disjoint dBD]
  have hunivsdiff : (Finset.univ \ (A' ∪ B' ∪ C' ∪ D')).card + (A' ∪ B' ∪ C' ∪ D').card = m := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  clear eA0 eA1 eB0 eB1 eC0 eC1 eD0 eD1 hAdef hBdef hCdef hDdef hpart hS0 hS1
    hH0sdiff hH1sdiff dAB dAC dAD dBC dBD dCD hH0 hH1 ha hb hc hd hA'sub hB'sub hC'sub hD'sub
  refine ⟨A' ∪ B' ∪ C' ∪ D', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

set_option maxHeartbeats 1000000 in
lemma two_agent_common_bivalued_safe_partition_cost_formula {m : ℕ} (u : Fin m → ℝ)
    (H : Finset (Fin m)) (r a : ℝ)
    (hu : ∀ g, u g = if g ∈ H then r * a else a) (S : Finset (Fin m)) :
    additive_valuation u S = a * ((S.card : ℝ) + (r - 1) * ((S ∩ H).card : ℝ)) := by
  have h1 : ∀ g ∈ S, u g = a + (if g ∈ H then (r - 1) * a else 0) := by
    intro g _
    rw [hu g]
    by_cases h : g ∈ H
    · simp only [h, if_true]; ring
    · simp only [h, if_false, add_zero]
  rw [additive_valuation, Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
lemma two_agent_common_bivalued_safe_partition_bundle_card_add (m : ℕ) (P : Fin m → Fin 2) :
    (bundle_of P 0).card + (bundle_of P 1).card = m := by
  have h := Finset.card_eq_sum_card_fiberwise (f := P) (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin 2))) (by intro x _; exact Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [Fin.sum_univ_two] at h
  simpa [bundle_of] using h.symm

set_option maxHeartbeats 1000000 in
lemma two_agent_common_bivalued_safe_partition_bundle_card_inter_add (m : ℕ) (P : Fin m → Fin 2)
    (H : Finset (Fin m)) :
    ((bundle_of P 0) ∩ H).card + ((bundle_of P 1) ∩ H).card = H.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := P) (s := H)
    (t := (Finset.univ : Finset (Fin 2))) (by intro x _; exact Finset.mem_univ _)
  rw [Fin.sum_univ_two] at h
  have e0 : (bundle_of P 0) ∩ H = H.filter (fun x => P x = 0) := by
    ext x; simp [bundle_of, and_comm]
  have e1 : (bundle_of P 1) ∩ H = H.filter (fun x => P x = 1) := by
    ext x; simp [bundle_of, and_comm]
  rw [e0, e1]
  exact h.symm

set_option maxHeartbeats 2000000 in
lemma two_agent_common_bivalued_safe_partition_mms_even {k m : ℕ} (hm : m = 2 * k) (r a : ℝ)
    (ha : 0 < a) (u : Fin m → ℝ) (H : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a) :
    a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2) ≤ chore_maximin_share 2 u := by
  rw [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hbdd : BddAbove (Set.range fun j : Fin 2 => additive_valuation u (bundle_of P j)) :=
    (Set.finite_range _).bddAbove
  have h0 : additive_valuation u (bundle_of P 0) ≤ ⨆ j, additive_valuation u (bundle_of P j) :=
    le_ciSup hbdd 0
  have h1 : additive_valuation u (bundle_of P 1) ≤ ⨆ j, additive_valuation u (bundle_of P j) :=
    le_ciSup hbdd 1
  have hc0 : (((bundle_of P 0).card : ℝ)) + ((bundle_of P 1).card : ℝ) = (m : ℝ) := by
    have := two_agent_common_bivalued_safe_partition_bundle_card_add m P
    exact_mod_cast this
  have hcH : (((bundle_of P 0) ∩ H).card : ℝ) + (((bundle_of P 1) ∩ H).card : ℝ) =
      (H.card : ℝ) := by
    have := two_agent_common_bivalued_safe_partition_bundle_card_inter_add m P H
    exact_mod_cast this
  have hsum : additive_valuation u (bundle_of P 0) + additive_valuation u (bundle_of P 1)
      = a * ((m : ℝ) + (r - 1) * (H.card : ℝ)) := by
    rw [two_agent_common_bivalued_safe_partition_cost_formula u H r a hu,
      two_agent_common_bivalued_safe_partition_cost_formula u H r a hu]
    have expand : a * (((bundle_of P 0).card : ℝ) + (r - 1) * (((bundle_of P 0) ∩ H).card : ℝ))
        + a * (((bundle_of P 1).card : ℝ) + (r - 1) * (((bundle_of P 1) ∩ H).card : ℝ))
        = a * ((((bundle_of P 0).card : ℝ) + ((bundle_of P 1).card : ℝ))
            + (r - 1) * ((((bundle_of P 0) ∩ H).card : ℝ)
              + (((bundle_of P 1) ∩ H).card : ℝ))) := by ring
    rw [expand, hc0, hcH]
  have hk : (m : ℝ) = 2 * (k : ℝ) := by rw [hm]; push_cast; ring
  nlinarith [h0, h1, hsum, ha, hk]

set_option maxHeartbeats 2000000 in
lemma two_agent_common_bivalued_safe_partition_mms_odd {k m : ℕ} (hm : m = 2 * k + 1) (r a : ℝ)
    (hr : 1 ≤ r) (ha : 0 < a) (u : Fin m → ℝ) (H : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a) :
    a * (((k : ℝ) + 1) + (r - 1) * (((H.card - k : ℕ) : ℝ))) ≤ chore_maximin_share 2 u := by
  rw [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hbdd : BddAbove (Set.range fun j : Fin 2 => additive_valuation u (bundle_of P j)) :=
    (Set.finite_range _).bddAbove
  have h0 : additive_valuation u (bundle_of P 0) ≤ ⨆ j, additive_valuation u (bundle_of P j) :=
    le_ciSup hbdd 0
  have h1 : additive_valuation u (bundle_of P 1) ≤ ⨆ j, additive_valuation u (bundle_of P j) :=
    le_ciSup hbdd 1
  have hc0 : (bundle_of P 0).card + (bundle_of P 1).card = m :=
    two_agent_common_bivalued_safe_partition_bundle_card_add m P
  have hr1 : (0:ℝ) ≤ r - 1 := by linarith
  have key : ∀ (b : Finset (Fin m)), k + 1 ≤ b.card →
      a * (((k : ℝ) + 1) + (r - 1) * (((H.card - k : ℕ) : ℝ))) ≤ additive_valuation u b := by
    intro b hbc
    have hbh : (H.card - k : ℕ) ≤ (b ∩ H).card := by
      have hsd : (H \ b).card = H.card - (b ∩ H).card := Finset.card_sdiff
      have hcomp : (H \ b).card + b.card ≤ m := by
        have h1 : (H \ b).card ≤ (Finset.univ \ b : Finset (Fin m)).card :=
          Finset.card_le_card (by
            intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
            exact hx.2)
        have h2 : (Finset.univ \ b : Finset (Fin m)).card + b.card = m := by
          rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b), Finset.card_univ,
            Fintype.card_fin]
        omega
      omega
    rw [two_agent_common_bivalued_safe_partition_cost_formula u H r a hu b]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    have e1 : ((k : ℝ) + 1) ≤ (b.card : ℝ) := by exact_mod_cast hbc
    have e2 : (((H.card - k : ℕ) : ℝ)) ≤ ((b ∩ H).card : ℝ) := by exact_mod_cast hbh
    have := mul_le_mul_of_nonneg_left e2 hr1
    linarith
  rcases Nat.lt_or_ge (bundle_of P 0).card (k + 1) with hlt | hge
  · have hb1 : k + 1 ≤ (bundle_of P 1).card := by omega
    have := key (bundle_of P 1) hb1
    linarith
  · have hb0 : k + 1 ≤ (bundle_of P 0).card := hge
    have := key (bundle_of P 0) hb0
    linarith

set_option maxHeartbeats 3000000 in
lemma two_agent_common_bivalued_safe_partition_agent_even {k m : ℕ} (hm : m = 2 * k) (hk : 1 ≤ k)
    (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a) (u : Fin m → ℝ) (H S : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a)
    (hs : S.card ≤ (m + 1) / 2) (hsc : (Finset.univ \ S).card ≤ (m + 1) / 2)
    (hh : (S ∩ H).card ≤ (H.card + 1) / 2) (hhc : (H \ S).card ≤ (H.card + 1) / 2) :
    additive_valuation u S ≤ ((r + 1) / 2) * chore_maximin_share 2 u ∧
    additive_valuation u (Finset.univ \ S) ≤ ((r + 1) / 2) * chore_maximin_share 2 u := by
  have hr1 : (0:ℝ) ≤ r - 1 := by linarith
  have h3 : (Finset.univ \ S).card = m - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hScard : S.card = k := by omega
  have hSccard : (Finset.univ \ S).card = k := by omega
  have hdel : (Finset.univ \ S) ∩ H = H \ S := by
    ext x; simp [and_comm]
  have hmms := two_agent_common_bivalued_safe_partition_mms_even hm r a ha u H hu
  have harith := bivalued_rounding_even_mms_arithmetic k H.card (r - 1) hk hr1
  have hbdd : (0:ℝ) ≤ ((r + 1) / 2) := by linarith
  have hmain : ∀ (T : Finset (Fin m)) (x y : ℝ), ((T.card : ℝ)) ≤ x →
      (((T ∩ H).card : ℝ)) ≤ y → additive_valuation u T ≤ a * (x + (r - 1) * y) := by
    intro T x y hx hy
    rw [two_agent_common_bivalued_safe_partition_cost_formula u H r a hu T]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    have := mul_le_mul_of_nonneg_left hy hr1
    linarith
  have h4 : ((r + 1) / 2) * (a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2))
      ≤ ((r + 1) / 2) * chore_maximin_share 2 u := mul_le_mul_of_nonneg_left hmms hbdd
  have h2 : a * ((k : ℝ) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ)))
      ≤ a * ((1 + (r - 1) / 2) * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left harith ha.le
  have key : a * ((1 + (r - 1) / 2) * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2))
      = ((r + 1) / 2) * (a * ((k : ℝ) + (r - 1) * (H.card : ℝ) / 2)) := by ring
  constructor
  · have h1 : additive_valuation u S ≤
        a * ((k : ℝ) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ))) := by
      refine hmain S (k : ℝ) ((((H.card + 1) / 2 : ℕ) : ℝ)) ?_ ?_
      · rw [hScard]
      · exact_mod_cast hh
    linarith
  · have h1 : additive_valuation u (Finset.univ \ S) ≤
        a * ((k : ℝ) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ))) := by
      refine hmain (Finset.univ \ S) (k : ℝ) ((((H.card + 1) / 2 : ℕ) : ℝ)) ?_ ?_
      · rw [hSccard]
      · rw [hdel]; exact_mod_cast hhc
    linarith

set_option maxHeartbeats 3000000 in
lemma two_agent_common_bivalued_safe_partition_agent_odd {k m : ℕ} (hm : m = 2 * k + 1)
    (r a : ℝ) (hr : 1 ≤ r) (ha : 0 < a) (u : Fin m → ℝ) (H S : Finset (Fin m))
    (hu : ∀ g, u g = if g ∈ H then r * a else a)
    (hs : S.card ≤ (m + 1) / 2) (hsc : (Finset.univ \ S).card ≤ (m + 1) / 2)
    (hh : (S ∩ H).card ≤ (H.card + 1) / 2) (hhc : (H \ S).card ≤ (H.card + 1) / 2) :
    additive_valuation u S ≤ ((r + 1) / 2) * chore_maximin_share 2 u ∧
    additive_valuation u (Finset.univ \ S) ≤ ((r + 1) / 2) * chore_maximin_share 2 u := by
  have hr1 : (0:ℝ) ≤ r - 1 := by linarith
  have hmms := two_agent_common_bivalued_safe_partition_mms_odd hm r a hr ha u H hu
  have harith := bivalued_rounding_odd_mms_arithmetic k H.card (r - 1) hr1
  have hbdd : (0:ℝ) ≤ ((r + 1) / 2) := by linarith
  have hdel : (Finset.univ \ S) ∩ H = H \ S := by ext x; simp [and_comm]
  have hmain : ∀ (T : Finset (Fin m)) (x y : ℝ), ((T.card : ℝ)) ≤ x →
      (((T ∩ H).card : ℝ)) ≤ y → additive_valuation u T ≤ a * (x + (r - 1) * y) := by
    intro T x y hx hy
    rw [two_agent_common_bivalued_safe_partition_cost_formula u H r a hu T]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    have := mul_le_mul_of_nonneg_left hy hr1
    linarith
  have hY : a * ((1 + (r - 1) / 2) * ((k : ℝ) + 1 + (r - 1) * (((H.card - k : ℕ) : ℝ))))
      = ((r + 1) / 2) * (a * ((k : ℝ) + 1 + (r - 1) * (((H.card - k : ℕ) : ℝ)))) := by ring
  have hmid : a * (((k : ℝ) + 1) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ)))
      ≤ ((r + 1) / 2) * (a * ((k : ℝ) + 1 + (r - 1) * (((H.card - k : ℕ) : ℝ)))) := by
    rw [← hY]; exact mul_le_mul_of_nonneg_left harith ha.le
  have h4 : ((r + 1) / 2) * (a * ((k : ℝ) + 1 + (r - 1) * (((H.card - k : ℕ) : ℝ))))
      ≤ ((r + 1) / 2) * chore_maximin_share 2 u := mul_le_mul_of_nonneg_left hmms hbdd
  constructor
  · have h1 : additive_valuation u S ≤
        a * (((k : ℝ) + 1) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ))) := by
      refine hmain S ((k : ℝ) + 1) ((((H.card + 1) / 2 : ℕ) : ℝ)) ?_ ?_
      · have : S.card ≤ k + 1 := by omega
        exact_mod_cast this
      · exact_mod_cast hh
    linarith
  · have h1 : additive_valuation u (Finset.univ \ S) ≤
        a * (((k : ℝ) + 1) + (r - 1) * ((((H.card + 1) / 2 : ℕ) : ℝ))) := by
      refine hmain (Finset.univ \ S) ((k : ℝ) + 1) ((((H.card + 1) / 2 : ℕ) : ℝ)) ?_ ?_
      · have h3 : (Finset.univ \ S).card = m - S.card := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        have : (Finset.univ \ S).card ≤ k + 1 := by omega
        exact_mod_cast this
      · rw [hdel]; exact_mod_cast hhc
    linarith

/-- Existence of a safe two-way partition for two agents with common bivalued chore costs, achieving at most ((r+1)/2) * MMS_i for both bundles and both agents. -/
theorem two_agent_common_bivalued_safe_partition
    (r : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (m : ℕ) (c : Fin 2 → Fin m → ℝ)
    (hc : is_scaled_bivalued_chores r c) :
    ∃ S : Finset (Fin m),
      ∀ i : Fin 2,
        additive_valuation (c i) S ≤ ((r + 1) / 2) * chore_maximin_share 2 (c i) ∧
        additive_valuation (c i) (Finset.univ \ S) ≤ ((r + 1) / 2) * chore_maximin_share 2 (c i) := by
  classical
  obtain ⟨a, ha, hv⟩ := hc
  let H : Fin 2 → Finset (Fin m) := fun i => Finset.univ.filter (fun g => c i g = r * a i)
  have hval (i : Fin 2) (g : Fin m) : c i g = if g ∈ H i then r * a i else a i := by
    by_cases h : c i g = r * a i
    · simp [H, h]
    · have hg := hv i g
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, h, if_false]
      exact hg.resolve_right h
  have halpha : (0:ℝ) ≤ (r + 1) / 2 := by linarith
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hHempty : ∀ i : Fin 2, H i = ∅ := by
      intro i
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x
      exact x.elim0
    have hzero : ∀ (i : Fin 2) (T : Finset (Fin 0)), additive_valuation (c i) T = 0 := by
      intro i T
      have hT : T = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x
        exact x.elim0
      rw [hT, additive_valuation, Finset.sum_empty]
    have hmms : ∀ i : Fin 2, (0:ℝ) ≤ chore_maximin_share 2 (c i) := by
      intro i
      have h := two_agent_common_bivalued_safe_partition_mms_even (k := 0) (m := 0)
        (rfl : (0:ℕ) = 2 * 0) r (a i) (ha i) (c i) (H i) (hval i)
      rw [hHempty i] at h
      simpa using h
    refine ⟨∅, fun i => ⟨?_, ?_⟩⟩
    · rw [hzero i ∅]; exact mul_nonneg halpha (hmms i)
    · rw [hzero i (Finset.univ \ (∅ : Finset (Fin 0)))]
      exact mul_nonneg halpha (hmms i)
  · obtain ⟨S, hs, hsc, h0, h0c, h1, h1c⟩ :=
      two_agent_common_bivalued_safe_partition_balance m (H 0) (H 1)
    refine ⟨S, fun i => ?_⟩
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmk : m = 2 * k := by omega
      have hk1 : 1 ≤ k := by omega
      fin_cases i
      · exact two_agent_common_bivalued_safe_partition_agent_even hmk hk1 r (a 0) hr1 (ha 0)
          (c 0) (H 0) S (hval 0) hs hsc h0 h0c
      · exact two_agent_common_bivalued_safe_partition_agent_even hmk hk1 r (a 1) hr1 (ha 1)
          (c 1) (H 1) S (hval 1) hs hsc h1 h1c
    · have hmk : m = 2 * k + 1 := by omega
      fin_cases i
      · exact two_agent_common_bivalued_safe_partition_agent_odd hmk r (a 0) hr1 (ha 0)
          (c 0) (H 0) S (hval 0) hs hsc h0 h0c
      · exact two_agent_common_bivalued_safe_partition_agent_odd hmk r (a 1) hr1 (ha 1)
          (c 1) (H 1) S (hval 1) hs hsc h1 h1c
