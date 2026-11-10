import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_uncomplemented_strongly_incomparable_lower_bound

Topic: combinatorics   Node: 01d378b20cea

Provenance: formalization of a published result. Source: arXiv:2611.12199 Proposition 4.2

Lower bound in Proposition 4.2 of arXiv:2611.12199: for all integers `n ≥ 3` and `3 ≤ t ≤ n`, there exists `𝒜 : Fin t → Finset (Finset (Fin n))` such that each `𝒜 i` is non-empty and uncomplemented, `𝒜` is strongly incomparable, and `2 ^ (n - 1) - 1 ≤ ∑ i : Fin t, (𝒜 i).card`.
-/

lemma op_1370_uncomplemented_strongly_incomparable_lower_bound_card_mem (n : ℕ) (z : Fin n) :
    (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X)).card = 2 ^ (n - 1) := by
  classical
  have h1 : (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X))
      = ((Finset.univ.erase z).powerset).image (fun Y => insert z Y) := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro hX
      refine ⟨X.erase z, ?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact (Finset.mem_erase.mp hy).1
      · exact Finset.insert_erase hX
    · rintro ⟨Y, hY, rfl⟩
      exact Finset.mem_insert_self _ _
  rw [h1]
  have hinj : Set.InjOn (fun Y : Finset (Fin n) => insert z Y) ↑((Finset.univ.erase z).powerset) := by
    intro Y hY Z hZ hYZ
    simp only [Finset.coe_powerset] at hY hZ
    have hY0 : z ∉ Y := fun h => by have := hY h; simp at this
    have hZ0 : z ∉ Z := fun h => by have := hZ h; simp at this
    have := congrArg (fun W => W.erase z) hYZ
    simpa only [Finset.erase_insert hY0, Finset.erase_insert hZ0] using this
  rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ z)]
  simp

lemma op_1370_uncomplemented_strongly_incomparable_lower_bound_card_large (n : ℕ) (z : Fin n) :
    (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card)).card ≤ n := by
  classical
  have hn1 : 1 ≤ n := by have := z.isLt; omega
  set S : Finset (Fin n) := Finset.univ.erase z with hS
  have hScard : S.card = n - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ z)]
    simp
  have hDsub : (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card))
      ⊆ insert Finset.univ (S.image (fun s => Finset.univ.erase s)) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨hzX, hcard⟩ := hX
    have hle : X.card ≤ n := by have := Finset.card_le_univ X; simpa using this
    have key : X = Finset.univ ∨ ∃ s ∈ S, Finset.univ.erase s = X := by
      rcases (show X.card = n ∨ X.card = n - 1 by omega) with h | h
      · left
        exact Finset.eq_univ_of_card X (by simpa using h)
      · right
        have hdiff : (Finset.univ \ X).card = 1 := by
          have hEq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
          rw [Finset.card_univ, Fintype.card_fin, h] at hEq
          omega
        obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hdiff
        have hsnt : s ∉ X := by
          have : s ∈ Finset.univ \ X := by rw [hs]; exact Finset.mem_singleton_self s
          exact (Finset.mem_sdiff.mp this).2
        have hXs : X = Finset.univ.erase s := by
          ext y
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · intro hy heq
            exact hsnt (heq ▸ hy)
          · intro hys
            by_contra hy
            have hy' : y ∈ Finset.univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
            rw [hs] at hy'
            exact hys (Finset.mem_singleton.mp hy')
        refine ⟨s, ?_, hXs.symm⟩
        simp only [hS, Finset.mem_erase, Finset.mem_univ, and_true]
        intro hsz
        rw [hsz] at hXs
        rw [hXs] at hzX
        simp at hzX
    rcases key with h | ⟨s, hs, hXs⟩
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [← hXs]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs)
  calc (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card)).card
      ≤ (insert Finset.univ (S.image (fun s => Finset.univ.erase s))).card :=
        Finset.card_le_card hDsub
    _ ≤ (S.image (fun s => Finset.univ.erase s)).card + 1 := Finset.card_insert_le _ _
    _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun s => Finset.univ.erase s); omega
    _ = n := by rw [hScard]; omega

/-- Lower bound in Proposition 4.2 of arXiv:2611.12199: there exist t non-empty uncomplemented strongly incomparable families of total size at least 2^(n-1) - 1. -/
theorem op_1370_uncomplemented_strongly_incomparable_lower_bound (n t : ℕ) (hn : 3 ≤ n) (ht : 3 ≤ t) (htn : t ≤ n) : ∃ 𝒜 : Fin t → Finset (Finset (Fin n)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ 2 ^ (n - 1) - 1 ≤ ∑ i, (𝒜 i).card := by
  classical
  obtain ⟨z, hzval⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  let S : Finset (Fin n) := Finset.univ.erase z
  let A1 : Finset (Finset (Fin n)) := Finset.univ.filter (fun X => z ∈ X ∧ X.card ≤ n - 2)
  let cls : Fin n → Fin (t - 1) := fun s => ⟨min (s.val - 1) (t - 2), by
    have := Nat.min_le_right (s.val - 1) (t - 2); omega⟩
  let G : Fin (t - 1) → Finset (Finset (Fin n)) := fun j => (S.filter (fun s => cls s = j)).image (fun s => S.erase s)
  let A' : Fin ((t-1)+1) → Finset (Finset (Fin n)) := Fin.cons (α := fun _ => Finset (Finset (Fin n))) A1 G
  let e : Fin t ≃ Fin ((t-1)+1) := finCongr (by omega : t = (t-1)+1)
  let A : Fin t → Finset (Finset (Fin n)) := fun i => A' (e i)
  have hSdef : S = Finset.univ.erase z := rfl
  have hA'0 : A' 0 = A1 := by simp only [A', Fin.cons_zero]
  have hA'succ : ∀ j : Fin (t-1), A' j.succ = G j := fun j => by simp only [A', Fin.cons_succ]
  have hScard : S.card = n - 1 := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ z)]; simp
  have hzS : z ∉ S := by rw [hSdef]; exact Finset.notMem_erase z _
  have memA1 : ∀ X, X ∈ A1 ↔ z ∈ X ∧ X.card ≤ n - 2 := by intro X; simp [A1]
  have memG : ∀ (j : Fin (t-1)) (X), X ∈ G j ↔ ∃ s, s ∈ S ∧ cls s = j ∧ S.erase s = X := by
    intro j X; simp only [G, Finset.mem_image, Finset.mem_filter]; tauto
  have z_notMem_G : ∀ (j : Fin (t-1)) (X), X ∈ G j → z ∉ X := by
    intro j X hX
    rw [memG] at hX
    obtain ⟨s, hs, hcls, rfl⟩ := hX
    exact fun h => hzS (Finset.mem_erase.mp h).2
  have card_G : ∀ (j : Fin (t-1)) (X), X ∈ G j → X.card = n - 2 := by
    intro j X hX
    rw [memG] at hX
    obtain ⟨s, hs, hcls, rfl⟩ := hX
    rw [Finset.card_erase_of_mem hs, hScard]; omega
  have hTinj : Set.InjOn (fun s => S.erase s) ↑S := by
    intro s hs s' hs' heq
    simp only at heq
    have h1 : s ∉ S.erase s := Finset.notMem_erase s S
    rw [heq] at h1
    by_contra hne
    exact h1 (Finset.mem_erase.mpr ⟨hne, hs⟩)
  have cls_surj : ∀ j : Fin (t-1), ∃ s, s ∈ S ∧ cls s = j := by
    intro j
    refine ⟨⟨j.val + 1, by have := j.isLt; omega⟩, ?_, ?_⟩
    · rw [hSdef, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have := congrArg Fin.val h
      simp only [hzval] at this
      omega
    · apply Fin.ext
      simp only [cls]
      have hmin : min ((j.val + 1) - 1) (t - 2) = j.val := by
        rw [Nat.add_sub_cancel]
        exact Nat.min_eq_left (by have := j.isLt; omega)
      rw [hmin]
  have G_ne : ∀ j : Fin (t-1), (G j).Nonempty := by
    intro j
    obtain ⟨s, hs, hcls⟩ := cls_surj j
    exact ⟨S.erase s, (memG j (S.erase s)).mpr ⟨s, hs, hcls, rfl⟩⟩
  have A1_ne : A1.Nonempty := by
    refine ⟨{z}, ?_⟩
    rw [memA1]
    exact ⟨Finset.mem_singleton_self z, by rw [Finset.card_singleton]; omega⟩
  have A'_ne : ∀ k : Fin ((t-1)+1), (A' k).Nonempty := by
    intro k
    induction k using Fin.cases with
    | zero => rw [hA'0]; exact A1_ne
    | succ j => rw [hA'succ j]; exact G_ne j
  have A'_unc : ∀ k : Fin ((t-1)+1), is_uncomplemented (A' k) := by
    intro k
    induction k using Fin.cases with
    | zero =>
      rw [hA'0]
      intro X hX hXc
      have hzX : z ∈ X := ((memA1 X).mp hX).1
      have hzXc : z ∈ Xᶜ := ((memA1 (Xᶜ)).mp hXc).1
      rw [Finset.mem_compl] at hzXc
      exact hzXc hzX
    | succ j =>
      rw [hA'succ j]
      intro X hX hXc
      have hzX : z ∉ X := z_notMem_G j X hX
      have hzXc : z ∉ Xᶜ := z_notMem_G j (Xᶜ) hXc
      rw [Finset.mem_compl] at hzXc
      exact hzXc hzX
  have A'_strong : strongly_incomparable A' := by
    intro i j hij
    obtain rfl | ⟨ii, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · obtain rfl | ⟨jj, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · exact absurd rfl hij
      · rw [hA'0, hA'succ jj]
        intro X hX Y hY hsub
        exact (z_notMem_G jj Y hY) (hsub ((memA1 X).mp hX).1)
    · obtain rfl | ⟨jj, rfl⟩ := Fin.eq_zero_or_eq_succ j
      · rw [hA'succ ii, hA'0]
        intro X hX Y hY hsub
        have hXc := card_G ii X hX
        have hYz : z ∈ Y := ((memA1 Y).mp hY).1
        have hYc : Y.card ≤ n - 2 := ((memA1 Y).mp hY).2
        have hzX : z ∉ X := z_notMem_G ii X hX
        have heq : X = Y := Finset.eq_of_subset_of_card_le hsub (by rw [hXc]; exact hYc)
        exact hzX (heq ▸ hYz)
      · rw [hA'succ ii, hA'succ jj]
        intro X hX Y hY hsub
        have hii : ii ≠ jj := fun h => hij (by rw [h])
        have hXc := card_G ii X hX
        have hYc := card_G jj Y hY
        rw [memG] at hX hY
        obtain ⟨s, hs, hcls, rfl⟩ := hX
        obtain ⟨s', hs', hcls', rfl⟩ := hY
        have hcard : (S.erase s).card = (S.erase s').card := by rw [hXc, hYc]
        have heq : S.erase s = S.erase s' := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
        have hss' : s = s' := hTinj hs hs' heq
        exact hii (by rw [← hcls, ← hcls', hss'])
  have hsum : ∑ i : Fin t, (A i).card = A1.card + ∑ j : Fin (t-1), (G j).card := by
    simp only [A]
    rw [Equiv.sum_comp e (fun k => (A' k).card)]
    rw [Fin.sum_univ_succ]
    rw [hA'0]
    simp only [hA'succ]
  have hGcard : ∀ j : Fin (t-1), (G j).card = (S.filter (fun s => cls s = j)).card := by
    intro j
    simp only [G]
    apply Finset.card_image_of_injOn
    intro s hs s' hs' heq
    exact hTinj (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs').1 heq
  have hfiber : S.card = ∑ j : Fin (t-1), (S.filter (fun s => cls s = j)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := cls) (s := S) (t := Finset.univ)
      (by intro x hx; exact Finset.mem_univ _)
    simpa using h
  have hGsum : ∑ j : Fin (t-1), (G j).card = n - 1 := by
    calc ∑ j : Fin (t-1), (G j).card
        = ∑ j : Fin (t-1), (S.filter (fun s => cls s = j)).card := Finset.sum_congr rfl (fun j _ => hGcard j)
      _ = S.card := hfiber.symm
      _ = n - 1 := hScard
  have hDsubB : (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card))
      ⊆ (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X)) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    exact hX.1
  have hA1eq : A1 = (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X)) \ (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card)) := by
    ext X
    simp only [A1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hzX, hcX⟩
      exact ⟨hzX, fun h => by omega⟩
    · rintro ⟨hzX, hnot⟩
      refine ⟨hzX, ?_⟩
      by_contra h
      exact hnot ⟨hzX, by omega⟩
  have hA1card : A1.card = 2^(n-1) - (Finset.univ.filter (fun X : Finset (Fin n) => z ∈ X ∧ n - 1 ≤ X.card)).card := by
    have hDeq := Finset.card_sdiff_add_card_eq_card hDsubB
    rw [hA1eq]
    rw [op_1370_uncomplemented_strongly_incomparable_lower_bound_card_mem] at hDeq
    omega
  have hDle := op_1370_uncomplemented_strongly_incomparable_lower_bound_card_large n z
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro i; exact A'_ne (e i)
  · intro i; exact A'_unc (e i)
  · intro i j hij X hX Y hY hsub
    exact A'_strong (e i) (e j) (fun h => hij (e.injective h)) X hX Y hY hsub
  · rw [hsum, hGsum, hA1card]
    have hpow : n ≤ 2^(n-1) := by have hlt : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self; omega
    omega
