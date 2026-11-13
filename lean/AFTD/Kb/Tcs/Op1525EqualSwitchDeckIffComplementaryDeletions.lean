import AFTD.Prelude

/-!
# op1525_equal_switch_deck_iff_complementary_deletions

Topic: combinatorics   Node: 439f53440f86

Provenance: helper lemma. The equal-part subset-deletion reformulation for OP-1525; compare arXiv:2611.13901, Section 4.1.

For equal-size complementary subsets, equality of their weak one-switch decks under a permutation group is equivalent to equality of the combined ordinary deletion decks of each subset and its complement.
-/

namespace Op1525Deck

/-- canonical (k-1)-set of the switched card `X △ {w}` -/
def er {V : Type*} [DecidableEq V] [Fintype V] (X : Finset V) (w : V) : Finset V :=
  if w ∈ X then X.erase w else (Finset.univ \ X).erase w

theorem mem_er {V : Type*} [DecidableEq V] [Fintype V] (X : Finset V) (w x : V) :
    x ∈ er X w ↔ xor (decide (x ∈ X)) (decide (x = w)) = decide (w ∈ X) := by
  unfold er
  by_cases hw : w ∈ X <;> by_cases hx : x = w
  · subst hx; simp [hw]
  · simp [hw, hx]
  · subst hx; simp [hw]
  · simp [hw, hx]

theorem er_card {V : Type*} [DecidableEq V] [Fintype V] (X : Finset V) (w : V) (k : ℕ) (hX : X.card = k)
    (hn : Fintype.card V = 2 * k) (hk : 1 ≤ k) : (er X w).card + 1 = k := by
  unfold er
  split_ifs with hw
  · rw [Finset.card_erase_of_mem hw]; omega
  · have hw' : w ∈ Finset.univ \ X := by simp [hw]
    rw [Finset.card_erase_of_mem hw', Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    omega

theorem compl_er_card {V : Type*} [DecidableEq V] [Fintype V] (X : Finset V) (w : V) (k : ℕ) (hX : X.card = k)
    (hn : Fintype.card V = 2 * k) (hk : 1 ≤ k) : (Finset.univ \ er X w).card = k + 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have := er_card X w k hX hn hk
  omega

/-- per-vertex reduction of the weak switch condition -/
theorem switch_iff {V : Type*} [DecidableEq V] [Fintype V] (A B : Finset V) (k : ℕ) (hk : 1 ≤ k) (hn : Fintype.card V = 2 * k)
    (hA : A.card = k) (hB : B.card = k) (g : Equiv.Perm V) (w w' : V) :
    (∃ d : Bool, ∀ x : V, xor (decide (g x ∈ A)) (decide (g x = w)) =
        xor (xor (decide (x ∈ B)) (decide (x = w'))) d) ↔
      (er B w').image g = er A w := by
  constructor
  · rintro ⟨d, hd⟩
    by_cases hdc : d = xor (decide (w ∈ A)) (decide (w' ∈ B))
    · ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_er] at hx ⊢
        have := hd x
        revert hx this; subst hdc
        generalize decide (g x ∈ A) = a1; generalize decide (g x = w) = a2
        generalize decide (x ∈ B) = b1; generalize decide (x = w') = b2
        generalize decide (w ∈ A) = c1; generalize decide (w' ∈ B) = c2
        revert a1 a2 b1 b2 c1 c2; decide
      · intro hy
        refine ⟨g.symm y, ?_, by simp⟩
        rw [mem_er] at hy ⊢
        have := hd (g.symm y)
        simp only [Equiv.apply_symm_apply] at this
        revert hy this; subst hdc
        generalize decide (y ∈ A) = a1; generalize decide (y = w) = a2
        generalize decide (g.symm y ∈ B) = b1; generalize decide (g.symm y = w') = b2
        generalize decide (w ∈ A) = c1; generalize decide (w' ∈ B) = c2
        revert a1 a2 b1 b2 c1 c2; decide
    · exfalso
      have heq : er A w = (Finset.univ \ er B w').image g := by
        ext y
        rw [Finset.mem_image]
        constructor
        · intro hy
          refine ⟨g.symm y, ?_, by simp⟩
          rw [Finset.mem_sdiff, mem_er]
          rw [mem_er] at hy
          have := hd (g.symm y)
          simp only [Equiv.apply_symm_apply] at this
          refine ⟨Finset.mem_univ _, ?_⟩
          clear hd
          revert hy this hdc
          generalize decide (y ∈ A) = a1; generalize decide (y = w) = a2
          generalize decide (g.symm y ∈ B) = b1; generalize decide (g.symm y = w') = b2
          generalize decide (w ∈ A) = c1; generalize decide (w' ∈ B) = c2
          revert a1 a2 b1 b2 c1 c2 d; decide
        · rintro ⟨x, hx, rfl⟩
          rw [Finset.mem_sdiff, mem_er] at hx
          replace hx := hx.2
          rw [mem_er]
          have := hd x
          clear hd
          revert hx this hdc
          generalize decide (g x ∈ A) = a1; generalize decide (g x = w) = a2
          generalize decide (x ∈ B) = b1; generalize decide (x = w') = b2
          generalize decide (w ∈ A) = c1; generalize decide (w' ∈ B) = c2
          revert a1 a2 b1 b2 c1 c2 d; decide
      have h1 := er_card A w k hA hn hk
      have h2 := compl_er_card B w' k hB hn hk
      rw [heq, Finset.card_image_of_injective _ g.injective] at h1
      omega
  · intro himg
    refine ⟨xor (decide (w ∈ A)) (decide (w' ∈ B)), fun x => ?_⟩
    have hiff : g x ∈ er A w ↔ x ∈ er B w' := by
      rw [← himg, g.injective.mem_finset_image]
    rw [mem_er, mem_er] at hiff
    revert hiff
    generalize decide (g x ∈ A) = a1; generalize decide (g x = w) = a2
    generalize decide (x ∈ B) = b1; generalize decide (x = w') = b2
    generalize decide (w ∈ A) = c1; generalize decide (w' ∈ B) = c2
    revert a1 a2 b1 b2 c1 c2; decide

/-- deleting one point of `T` gives `R` for exactly one point when `R ⊆ T` -/
theorem del_count {V : Type*} [DecidableEq V] (T R : Finset V) (h : R.card + 1 = T.card) :
    (T.filter (fun t => T.erase t = R)).card = if R ⊆ T then 1 else 0 := by
  split_ifs with hRT
  · have : T.filter (fun t => T.erase t = R) = T \ R := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨ht, hte⟩
        refine ⟨ht, fun htR => ?_⟩
        rw [← hte] at htR; simp at htR
      · rintro ⟨ht, htR⟩
        refine ⟨ht, ?_⟩
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun hxt => htR (hxt ▸ hx), hRT hx⟩
        · rw [Finset.card_erase_of_mem ht]; omega
    rw [this, Finset.card_sdiff_of_subset hRT]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ hte
    exact hRT (hte ▸ Finset.erase_subset t T)

theorem card_comp_perm {γ : Type*} [Fintype γ] (Φ : γ ≃ γ) (f : γ → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun p => f (Φ p))).card = (Finset.univ.filter f).card := by
  refine Finset.card_nbij' Φ Φ.symm ?_ ?_ (fun p _ => Φ.symm_apply_apply p)
    (fun p _ => Φ.apply_symm_apply p)
  · intro p hp; simpa using hp
  · intro p hp; simpa using hp

theorem erase_image_count {V : Type*} [DecidableEq V] (X R : Finset V) (g : Equiv.Perm V)
    (h : R.card + 1 = X.card) :
    (X.filter (fun w => (X.erase w).image g = R)).card = if R ⊆ X.image g then 1 else 0 := by
  rw [← del_count (X.image g) R (by rw [Finset.card_image_of_injective _ g.injective]; exact h)]
  rw [Finset.filter_image, Finset.card_image_of_injective _ g.injective]
  congr 1
  apply Finset.filter_congr
  intro w _
  simp only [Finset.image_erase g.injective]

theorem summand_eq {V : Type*} [DecidableEq V] [Fintype V] (A R : Finset V) (k : ℕ)
    (hk : 1 ≤ k) (hn : Fintype.card V = 2 * k) (hA : A.card = k) (hR : R.card + 1 = k)
    (g : Equiv.Perm V) :
    (Finset.univ.filter (fun w => (er A w).image g = R)).card =
      (if R ⊆ A.image g then 1 else 0) + (if R ⊆ (Finset.univ \ A).image g then 1 else 0) := by
  have hAc : (Finset.univ \ A).card = k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; omega
  rw [← erase_image_count A R g (by omega), ← erase_image_count (Finset.univ \ A) R g (by omega)]
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun w => (er A w).image g = R)) (fun w => w ∈ A)]
  congr 1
  · congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩; rwa [er, if_pos h2] at h1
    · rintro ⟨h2, h1⟩; refine ⟨?_, h2⟩; rwa [er, if_pos h2]
  · congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩; rwa [er, if_neg h2] at h1
    · rintro ⟨h2, h1⟩; refine ⟨?_, h2⟩; rwa [er, if_neg h2]

/-- orbit of a set under `H` -/
def orb {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (S : Finset V) : Finset (Finset V) :=
  Finset.univ.image (fun g : H => S.image g.1)

theorem mem_orb {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (S T : Finset V) : T ∈ orb H S ↔ ∃ g : H, S.image g.1 = T := by
  simp [orb]

theorem image_mul {V : Type*} [DecidableEq V] (S : Finset V) (g h : Equiv.Perm V) :
    (S.image h).image g = S.image (g * h) := by
  rw [Finset.image_image]; rfl

theorem imH {V : Type*} [DecidableEq V] {H : Subgroup (Equiv.Perm V)} (S : Finset V)
    (g h : H) : (S.image h.1).image g.1 = S.image (g * h).1 := by
  rw [Finset.image_image]; rfl

theorem orb_eq_iff {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (S T : Finset V) : orb H S = orb H T ↔ ∃ g : H, S.image g.1 = T := by
  constructor
  · intro h
    have : T ∈ orb H S := by rw [h, mem_orb]; exact ⟨1, by simp⟩
    exact (mem_orb H S T).mp this
  · rintro ⟨h, rfl⟩
    ext X
    rw [mem_orb, mem_orb]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g * h⁻¹, by rw [imH, inv_mul_cancel_right]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g * h, by rw [← imH]⟩

theorem orb_self {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (S : Finset V) : S ∈ orb H S := (mem_orb H S S).mpr ⟨1, by simp⟩

/-- number of group elements carrying `S` onto `R` -/
theorem carry_count {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (S R : Finset V) :
    (Finset.univ.filter (fun g : H => S.image g.1 = R)).card =
      if orb H S = orb H R then (Finset.univ.filter (fun g : H => R.image g.1 = R)).card
      else 0 := by
  split_ifs with ho
  · obtain ⟨h, rfl⟩ := (orb_eq_iff H S R).mp ho
    refine Finset.card_nbij' (fun g => g * h⁻¹) (fun g => g * h) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [imH, inv_mul_cancel_right]; exact hg
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [← imH]; exact hg
    · intro g _; simp
    · intro g _; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _ hg
    exact ho ((orb_eq_iff H S R).mpr ⟨g, hg⟩)

theorem stab_pos {V : Type*} [DecidableEq V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (R : Finset V) : 0 < (Finset.univ.filter (fun g : H => R.image g.1 = R)).card :=
  Finset.card_pos.mpr ⟨1, by simp⟩

/-- the orbit-incidence sum factors as stabilizer size times orbit count -/
theorem sum_eq {V : Type*} [DecidableEq V] [Fintype V] (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (A R : Finset V) :
    (∑ g : H, (Finset.univ.filter (fun w => (er A w).image g.1 = R)).card) =
      (Finset.univ.filter (fun g : H => R.image g.1 = R)).card *
        (Finset.univ.filter (fun w => orb H (er A w) = orb H R)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.card_filter, carry_count]
  split_ifs <;> simp

end Op1525Deck

theorem op1525_equal_switch_deck_iff_complementary_deletions
    {V : Type*} [DecidableEq V] [Fintype V]
    (H : Subgroup (Equiv.Perm V)) [Fintype H]
    (A B : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hn : Fintype.card V = 2 * k)
    (hA : A.card = k) (hB : B.card = k) :
    (∃ π : Equiv.Perm V, ∀ w : V, ∃ g : H, ∃ d : Bool, ∀ x : V,
      xor (decide (g.1 x ∈ A)) (decide (g.1 x = w)) =
        xor (xor (decide (x ∈ B)) (decide (x = π w))) d) ↔
    (∀ R : Finset V, R.card + 1 = k →
      (∑ g : H, ((if R ⊆ A.image g.1 then (1 : ℤ) else 0) +
                   (if R ⊆ (Finset.univ \ A).image g.1 then 1 else 0))) =
      ∑ g : H, ((if R ⊆ B.image g.1 then (1 : ℤ) else 0) +
                  (if R ⊆ (Finset.univ \ B).image g.1 then 1 else 0))) := by
  classical
  open Op1525Deck in
  -- reduce the left side to orbit equalities
  have hL : (∃ π : Equiv.Perm V, ∀ w : V, ∃ g : H, ∃ d : Bool, ∀ x : V,
      xor (decide (g.1 x ∈ A)) (decide (g.1 x = w)) =
        xor (xor (decide (x ∈ B)) (decide (x = π w))) d) ↔
      ∃ π : Equiv.Perm V, ∀ w, orb H (er B (π w)) = orb H (er A w) := by
    refine exists_congr (fun π => forall_congr' (fun w => ?_))
    rw [orb_eq_iff]
    exact exists_congr (fun g => switch_iff A B k hk hn hA hB g.1 w (π w))
  -- reduce the right side to orbit counts
  have hcnt : ∀ (X : Finset V), X.card = k → ∀ R : Finset V, R.card + 1 = k →
      (∑ g : H, ((if R ⊆ X.image g.1 then (1 : ℤ) else 0) +
                   (if R ⊆ (Finset.univ \ X).image g.1 then 1 else 0))) =
      (((Finset.univ.filter (fun g : H => R.image g.1 = R)).card *
        (Finset.univ.filter (fun w => orb H (er X w) = orb H R)).card : ℕ) : ℤ) := by
    intro X hX R hR
    rw [← sum_eq H X R]
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    rw [summand_eq X R k hk hn hX hR g.1]
    split_ifs <;> simp
  have hR : (∀ R : Finset V, R.card + 1 = k →
      (∑ g : H, ((if R ⊆ A.image g.1 then (1 : ℤ) else 0) +
                   (if R ⊆ (Finset.univ \ A).image g.1 then 1 else 0))) =
      ∑ g : H, ((if R ⊆ B.image g.1 then (1 : ℤ) else 0) +
                  (if R ⊆ (Finset.univ \ B).image g.1 then 1 else 0))) ↔
      ∀ R : Finset V, R.card + 1 = k →
        (Finset.univ.filter (fun w => orb H (er A w) = orb H R)).card =
        (Finset.univ.filter (fun w => orb H (er B w) = orb H R)).card := by
    refine forall_congr' (fun R => imp_congr_right (fun hR => ?_))
    rw [hcnt A hA R hR, hcnt B hB R hR, Nat.cast_inj]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_left (stab_pos H R) h, fun h => by rw [h]⟩
  rw [hL, hR]
  constructor
  · rintro ⟨π, hπ⟩ R _
    rw [← card_comp_perm π (fun w => orb H (er B w) = orb H R)]
    congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hπ w]
  · intro hc
    have hfib : ∀ O : Finset (Finset V),
        Fintype.card {w // orb H (er A w) = O} = Fintype.card {w // orb H (er B w) = O} := by
      intro O
      rw [Fintype.card_subtype, Fintype.card_subtype]
      by_cases hOA : ∃ w0, orb H (er A w0) = O
      · obtain ⟨w0, rfl⟩ := hOA
        exact hc _ (er_card A w0 k hA hn hk)
      · by_cases hOB : ∃ w1, orb H (er B w1) = O
        · obtain ⟨w1, rfl⟩ := hOB
          exact (hc _ (er_card B w1 k hB hn hk))
        · push Not at hOA hOB
          rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun w _ => hOA w)),
            Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun w _ => hOB w))]
    let e : ∀ O, {w // orb H (er A w) = O} ≃ {w // orb H (er B w) = O} :=
      fun O => Fintype.equivOfCardEq (hfib O)
    refine ⟨Equiv.ofFiberEquiv e, fun w => ?_⟩
    exact Equiv.ofFiberEquiv_map e w
