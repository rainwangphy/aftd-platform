import AFTD.Prelude

/-!
# matroid_finset_indep_extend_to_card

Topic: combinatorics   Node: ba92474b13c5

Provenance: helper lemma.

An independent finite set can be extended to an independent set of any cardinality realized by a larger independent set.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN800GeneralMatroid

lemma extend_to_card {V : Type*} [Fintype V] [DecidableEq V] (M : Matroid V)
    (I J : Finset V) (hI : M.Indep (I : Set V)) (hJ : M.Indep (J : Set V))
    (hcard : I.card ≤ J.card) :
    ∃ K : Finset V, I ⊆ K ∧ K.card = J.card ∧ M.Indep (K : Set V) := by
  have go : ∀ d (P : Finset V), M.Indep (P : Set V) → P.card ≤ J.card →
      J.card - P.card = d → ∃ K : Finset V, P ⊆ K ∧ K.card = J.card ∧ M.Indep (K : Set V) := by
    intro d
    induction d with
    | zero =>
      intro P hP hle hd
      refine ⟨P, by intro x hx; exact hx, ?_, hP⟩
      omega
    | succ d ih =>
      intro P hP hle hd
      have hlt : P.card < J.card := by omega
      obtain ⟨x, hxJ, hxP, hxInd⟩ := hP.augment_finset hJ hlt
      have hnewCard : (insert x P).card = P.card + 1 := Finset.card_insert_of_notMem hxP
      have hnewLe : (insert x P).card ≤ J.card := by omega
      have hnewDiff : J.card - (insert x P).card = d := by omega
      have hnewInd : M.Indep ((insert x P : Finset V) : Set V) := by
        simpa only [Finset.coe_insert] using hxInd
      obtain ⟨K, hPK, hKcard, hKind⟩ := ih (insert x P) hnewInd hnewLe hnewDiff
      refine ⟨K, ?_, hKcard, hKind⟩
      exact (Finset.subset_insert x P).trans hPK
  exact go (J.card - I.card) I hI hcard rfl

theorem all_pairs_not_two_codim_one {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matroid V) (hn : 4 ≤ Fintype.card V)
    (h2 : {W : Finset V | W.card = 2 ∧ M.Indep (W : Set V)}.ncard =
      Nat.choose (Fintype.card V) 2) :
    {W : Finset V | W.card = Fintype.card V - 1 ∧ M.Indep (W : Set V)}.ncard ≠ 2 := by
  classical
  let pairs : Finset (Finset V) := (Finset.univ : Finset V).powersetCard 2
  let goodPairs : Finset (Finset V) := pairs.filter (fun W => M.Indep (W : Set V))
  have hpairs : pairs.card = Nat.choose (Fintype.card V) 2 := by
    simp [pairs]
  have hgoodPairs : goodPairs.card = Nat.choose (Fintype.card V) 2 := by
    rw [Set.ncard_eq_toFinset_card'] at h2
    have heq : ({W : Finset V | W.card = 2 ∧ M.Indep (W : Set V)} : Set (Finset V)).toFinset = goodPairs := by
      ext W
      simp [goodPairs, pairs]
    rw [heq] at h2
    exact h2
  have heqPairs : goodPairs = pairs :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have allPairs (P : Finset V) (hP : P.card = 2) : M.Indep (P : Set V) := by
    have hmem : P ∈ pairs := by simp [pairs, hP]
    rw [← heqPairs] at hmem
    exact (Finset.mem_filter.mp hmem).2
  intro h3
  let codim : Finset (Finset V) :=
    Finset.univ.filter (fun W => W.card = Fintype.card V - 1 ∧ M.Indep (W : Set V))
  have hcnt : codim.card = 2 := by
    rw [Set.ncard_eq_toFinset_card'] at h3
    convert h3 using 1 <;> simp [codim]
  obtain ⟨A, B, hAB, hcodim⟩ := Finset.card_eq_two.mp hcnt
  have hA : A ∈ codim := by rw [hcodim]; simp
  have hB : B ∈ codim := by rw [hcodim]; simp
  have hAprops := (Finset.mem_filter.mp hA).2
  have hBprops := (Finset.mem_filter.mp hB).2
  have hAc : ((Finset.univ : Finset V) \ A).card = 1 := by
    simp [Finset.card_sdiff, hAprops.1]
    omega
  have hBc : ((Finset.univ : Finset V) \ B).card = 1 := by
    simp [Finset.card_sdiff, hBprops.1]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAc
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBc
  have haA : a ∉ A := by
    have : a ∈ (Finset.univ : Finset V) \ A := by rw [ha]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hbB : b ∉ B := by
    have : b ∈ (Finset.univ : Finset V) \ B := by rw [hb]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hab : a ≠ b := by
    intro h
    subst b
    have hc : (Finset.univ : Finset V) \ A = Finset.univ \ B := ha.trans hb.symm
    apply hAB
    ext x
    have hx := congrArg (fun S : Finset V => x ∈ S) hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    exact not_iff_not.mp (Iff.of_eq hx)
  let P : Finset V := {a,b}
  have hPc : P.card = 2 := by simp [P, hab]
  have hPi := allPairs P hPc
  obtain ⟨K, hPK, hKc, hKi⟩ := extend_to_card M P A hPi hAprops.2 (by omega)
  have hK : K ∈ codim := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by omega, hKi⟩
  rw [hcodim] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with hK | hK
  · have : a ∈ A := by rw [← hK]; exact hPK (by simp [P])
    exact haA this
  · have : b ∈ B := by rw [← hK]; exact hPK (by simp [P])
    exact hbB this

end IN800GeneralMatroid

theorem matroid_finset_indep_extend_to_card {V : Type*} [Fintype V] [DecidableEq V] (M : Matroid V) (I J : Finset V) (hI : M.Indep (I : Set V)) (hJ : M.Indep (J : Set V)) (hcard : I.card ≤ J.card) : ∃ K : Finset V, I ⊆ K ∧ K.card = J.card ∧ M.Indep (K : Set V) := by
  exact IN800GeneralMatroid.extend_to_card M I J hI hJ hcard
