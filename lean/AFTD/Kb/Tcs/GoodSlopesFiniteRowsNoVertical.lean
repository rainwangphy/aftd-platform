import AFTD.Prelude

/-!
# good_slopes_finite_rows_no_vertical

Topic: combinatorics   Node: d727148ed898

Provenance: helper lemma. Generic slice-counting step for OP-1027.

A finite set has p rows and p columns, each of size q. Each x-fiber has size at most rp and each row-column-x fiber size at most r. On each column x is constant or injective. If 2q exceeds rp and q is at least p+r, x is not constant on any row.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_finite_rows_no_vertical
    {α ι κ : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι] [DecidableEq κ]
    (S : Finset α) (row col : α → ι) (x : α → κ) (p q r : ℕ)
    (hp : Fintype.card ι = p) (hsize : r*p < 2*q) (hgap : p+r ≤ q)
    (hrows : ∀ i, (S.filter fun z => row z = i).card = q)
    (hcols : ∀ j, (S.filter fun z => col z = j).card = q)
    (hbound : ∀ k, (S.filter fun z => x z = k).card ≤ r*p)
    (hcross : ∀ i j k, (S.filter fun z => row z = i ∧ col z = j ∧ x z = k).card ≤ r)
    (hclass : ∀ j, (∃ k, ∀ z ∈ S, col z = j → x z = k) ∨
      Set.InjOn x {z | z ∈ S ∧ col z = j}) :
    ∀ i k, ¬ ∀ z ∈ S, row z = i → x z = k := by
  classical
  intro i k hrow
  let A := S.filter fun z => row z = i
  let B (j : ι) := A.filter fun z => col z = j
  have hA : A.card = q := hrows i
  have hAk : ∀ z ∈ A, x z = k := by
    intro z hz
    exact hrow z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  have hBbound (j : ι) : (B j).card ≤ r := by
    apply le_trans (Finset.card_le_card ?_) (hcross i j k)
    intro z hz
    have hzB := Finset.mem_filter.mp hz
    have hzA := Finset.mem_filter.mp hzB.1
    exact Finset.mem_filter.mpr ⟨hzA.1, hzA.2, hzB.2, hAk z hzB.1⟩
  have hAsum : A.card = ∑ j : ι, (B j).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hq : 0 < q := by omega
  by_cases hr : r = 0
  · have hz : ∀ j, (B j).card = 0 := by intro j; have := hBbound j; omega
    rw [hAsum] at hA
    simp [hz] at hA
    omega
  have hUnique {j j' : ι}
      (hj : ∀ z ∈ S, col z = j → x z = k)
      (hj' : ∀ z ∈ S, col z = j' → x z = k) : j = j' := by
    by_contra hne
    let C := S.filter fun z => col z = j
    let D := S.filter fun z => col z = j'
    have hdisj : Disjoint C D := by
      apply Finset.disjoint_left.mpr
      intro z hzC hzD
      have hc := (Finset.mem_filter.mp hzC).2
      have hd := (Finset.mem_filter.mp hzD).2
      exact hne (hc.symm.trans hd)
    have hsub : C ∪ D ⊆ S.filter fun z => x z = k := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hh := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hh.1, hj z hh.1 hh.2⟩
      · have hh := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hh.1, hj' z hh.1 hh.2⟩
    have h := (Finset.card_le_card hsub).trans (hbound k)
    rw [Finset.card_union_of_disjoint hdisj] at h
    have hC : C.card = q := hcols j
    have hD : D.card = q := hcols j'
    omega
  have hsmall (j : ι) (hn : ¬ ∀ z ∈ S, col z = j → x z = k) : (B j).card ≤ 1 := by
    rcases hclass j with ⟨v,hv⟩ | hv
    · have hvne : v ≠ k := by
        intro h
        apply hn
        intro z hz hcol
        rw [← h]
        exact hv z hz hcol
      have hempty : B j = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzB := Finset.mem_filter.mp hz
        have hzA := Finset.mem_filter.mp hzB.1
        exact hvne ((hv z hzA.1 hzB.2).symm.trans (hAk z hzB.1))
      simp [hempty]
    · apply Finset.card_le_one_iff.mpr
      intro z z' hz hz'
      have hzB := Finset.mem_filter.mp hz
      have hz'B := Finset.mem_filter.mp hz'
      have hzA := Finset.mem_filter.mp hzB.1
      have hz'A := Finset.mem_filter.mp hz'B.1
      exact hv ⟨hzA.1,hzB.2⟩ ⟨hz'A.1,hz'B.2⟩ ((hAk z hzB.1).trans (hAk z' hz'B.1).symm)
  by_cases he : ∃ j, ∀ z ∈ S, col z = j → x z = k
  · obtain ⟨j,hj⟩ := he
    have hRest : ∑ j' ∈ (Finset.univ : Finset ι).erase j, (B j').card ≤ p-1 := by
      calc
        _ ≤ ∑ _j' ∈ (Finset.univ : Finset ι).erase j, 1 := by
          apply Finset.sum_le_sum
          intro j' hj'
          have hjne : j' ≠ j := (Finset.mem_erase.mp hj').1
          apply hsmall
          intro hj'
          exact hjne (hUnique hj' hj)
        _ = p-1 := by simp [hp]
    have hs : (B j).card + ∑ j' ∈ (Finset.univ : Finset ι).erase j, (B j').card = A.card := by
      calc
        _ = ∑ j' : ι, (B j').card := Finset.add_sum_erase Finset.univ (fun j' => (B j').card) (Finset.mem_univ j)
        _ = A.card := hAsum.symm
    have hp0 : 0 < p := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
      omega
    have hb := hBbound j
    omega
  · have hs : A.card ≤ p := by
      rw [hAsum]
      calc
        _ ≤ ∑ _j : ι, 1 := by
          apply Finset.sum_le_sum
          intro j _
          apply hsmall
          intro hj
          exact he ⟨j,hj⟩
        _ = p := by simp [hp]
    omega
