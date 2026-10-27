import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordRestrictSupport
import AFTD.Kb.Tcs.BinaryPartialWordPartitionRestrict
import AFTD.Kb.Tcs.BinaryPartialWordPartitionSingularCoordinate
import AFTD.Kb.Tcs.BinaryPartialWordPartitionTwins
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# binary_partial_word_partition_order_convex

Topic: combinatorics   Node: 9d0e6ea049ca

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

In a finite Boolean cube partition with one more part than mentioned coordinates, linearly order the parts so that every false occurrence of a coordinate precedes every true occurrence. Then the parts mentioning any given coordinate form an order-convex set.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_order_convex (n : ℕ)
    {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
    (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (hessential : ∀ v, ∃ i, v ∈ s i)
    (hsize : Fintype.card V = n)
    (hcard : Fintype.card I = Fintype.card V + 1)
    (horder : ∀ v i j, v ∈ s i → v ∈ s j → b i v = false → b j v = true → i < j) :
    ∀ v i j k, i ≤ j → j ≤ k → v ∈ s i → v ∈ s k → v ∈ s j := by
  classical
  induction n using Nat.strong_induction_on generalizing I V with
  | h n ih =>
    by_cases hn : n = 0
    · have hV : Fintype.card V = 0 := hsize.trans hn
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      intro v
      exact isEmptyElim v
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hsing⟩ := binary_partial_word_partition_singular_coordinate
      s b hconflict hcover hessential hcard
    obtain ⟨i₀, i₁, hne, hv₀, hb₀, hv₁, hb₁, honly, hsame, hbits⟩ :=
      binary_partial_word_partition_twins s b hconflict hcover v hsing
    have h₀₁ : i₀ < i₁ := horder v i₀ i₁ hv₀ hv₁ hb₀ hb₁
    have hadj (j : I) (h₀j : i₀ < j) (hj₁ : j < i₁) : False := by
      obtain ⟨w, hw, hdiff⟩ := hconflict i₀ j (ne_of_lt h₀j)
      have hwv : w ≠ v := by
        intro he
        subst w
        rcases honly j (mem_inter.mp hw).2 with hj | hj
        · exact (ne_of_gt h₀j) hj
        · exact (ne_of_lt hj₁) hj
      have hwi₁ : w ∈ s i₁ := hsame ▸ (mem_inter.mp hw).1
      have hbitse := hbits w (mem_inter.mp hw).1 hwv
      cases hb : b i₀ w
      · have hbj : b j w = true := by
          cases hbj : b j w
          · exact (hdiff (hb.trans hbj.symm)).elim
          · rfl
        have hbi₁ : b i₁ w = false := hbitse.symm.trans hb
        exact (not_lt_of_gt hj₁) (horder w i₁ j hwi₁ (mem_inter.mp hw).2 hbi₁ hbj)
      · have hbj : b j w = false := by
          cases hbj : b j w
          · rfl
          · exact (hdiff (hb.trans hbj.symm)).elim
        exact (not_lt_of_gt h₀j) (horder w j i₀ (mem_inter.mp hw).2
          (mem_inter.mp hw).1 hbj hb)
    let J := {i : I // v ∉ s i ∨ b i v = false}
    let W := {w : V // w ≠ v}
    let t : J → Finset W := fun i => binary_partial_word_restrict_support (s i.val) v
    let c : J → W → Bool := fun i w => b i.val w.val
    have hsurv (i : I) (hi : i ≠ i₁) : v ∉ s i ∨ b i v = false := by
      by_cases hvi : v ∈ s i
      · right
        have hi₀ : i = i₀ := (honly i hvi).resolve_right hi
        simpa only [hi₀] using hb₀
      · exact Or.inl hvi
    let π : I → J := fun i => if h : i = i₁ then ⟨i₀, Or.inr hb₀⟩ else ⟨i, hsurv i h⟩
    have hπmono : Monotone π := by
      intro i j hij
      change (π i).val ≤ (π j).val
      by_cases hi : i = i₁
      · by_cases hj : j = i₁
        · simp [π, hi, hj]
        · have h₀j : i₀ ≤ j := h₀₁.le.trans (hi ▸ hij)
          simpa only [π, dif_pos hi, dif_neg hj] using h₀j
      · by_cases hj : j = i₁
        · have hi₁ : i < i₁ := lt_of_le_of_ne (hj ▸ hij) hi
          have hi₀ : i ≤ i₀ := le_of_not_gt (fun h₀i => hadj i h₀i hi₁)
          simpa only [π, dif_neg hi, dif_pos hj] using hi₀
        · simpa only [π, dif_neg hi, dif_neg hj] using hij
    have hπmem (w : W) (i : I) : w ∈ t (π i) ↔ w.val ∈ s i := by
      by_cases hi : i = i₁
      · subst i
        simp only [π, dif_pos rfl, t, binary_partial_word_restrict_support, mem_filter,
          mem_univ, true_and]
        rw [hsame]
      · simp only [π, dif_neg hi, t, binary_partial_word_restrict_support,
          mem_filter, mem_univ, true_and]
    have hr := binary_partial_word_partition_restrict s b hconflict hcover v false
    have hess : ∀ w : W, ∃ i : J, w ∈ t i := by
      intro w
      obtain ⟨i, hi⟩ := hessential w.val
      exact ⟨π i, (hπmem w i).mpr hi⟩
    have hW : Fintype.card W = Fintype.card V - 1 := by
      simpa only [W, Fintype.card_subtype_eq] using
        Fintype.card_subtype_compl (fun w : V => w = v)
    have hJ : Fintype.card J + 1 = Fintype.card I := by
      rw [Fintype.card_subtype]
      have he : (univ.filter (fun i : I => ¬(v ∉ s i ∨ b i v = false))) =
          univ.filter (fun i => v ∈ s i ∧ b i v = true) := by
        ext i
        by_cases hv : v ∈ s i
        · cases hb : b i v <;> simp [hv, hb]
        · simp [hv]
      have hc := card_filter_add_card_filter_not (s := univ)
        (fun i : I => v ∉ s i ∨ b i v = false)
      simpa only [he, hsing true, card_univ] using hc
    have hcard' : Fintype.card J = Fintype.card W + 1 := by omega
    have hlt : Fintype.card W < n := by omega
    have horder' : ∀ w (i j : J), w ∈ t i → w ∈ t j →
        c i w = false → c j w = true → i < j := by
      intro w i j hi hj hbi hbj
      apply horder w.val i.val j.val
      · exact (mem_filter.mp hi).2
      · exact (mem_filter.mp hj).2
      · exact hbi
      · exact hbj
    have hind := ih (Fintype.card W) hlt t c hr.1 hr.2 hess rfl hcard' horder'
    intro w i j k hij hjk hwi hwk
    by_cases hwv : w = v
    · subst w
      have h₀i : i₀ ≤ i := by
        rcases honly i hwi with hi | hi
        · exact hi.symm.le
        · simpa only [hi] using h₀₁.le
      have hk₁ : k ≤ i₁ := by
        rcases honly k hwk with hk | hk
        · simpa only [hk] using h₀₁.le
        · exact hk.le
      have h₀j : i₀ ≤ j := h₀i.trans hij
      have hj₁ : j ≤ i₁ := hjk.trans hk₁
      by_cases hj₀ : j = i₀
      · simpa only [hj₀] using hv₀
      by_cases hj₁eq : j = i₁
      · simpa only [hj₁eq] using hv₁
      exact (hadj j (lt_of_le_of_ne h₀j (Ne.symm hj₀)) (lt_of_le_of_ne hj₁ hj₁eq)).elim
    · have hs := hind ⟨w, hwv⟩ (π i) (π j) (π k) (hπmono hij) (hπmono hjk)
        ((hπmem ⟨w, hwv⟩ i).mpr hwi) ((hπmem ⟨w, hwv⟩ k).mpr hwk)
      exact (hπmem ⟨w, hwv⟩ j).mp hs
