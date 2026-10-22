import AFTD.Prelude

/-!
# cyclic_necklace_transitions_ge_two_mul_sub_one

Topic: fair_division   Node: 2029d9218100

Provenance: helper lemma. arXiv:2610.27956 Proposition 1

On a cyclic necklace of r red beads followed by b blue beads with r, b ≥ k ≥ 2, any allocation to k agents in which every agent receives at least one red bead and at least one blue bead has at least 2(k - 1) index transitions where adjacent beads are assigned to different agents.
-/

open Finset in
lemma cyclic_necklace_transitions_ge_two_mul_sub_one_changes_succ {β : Type*} [DecidableEq β]
    (f : ℕ → β) (n : ℕ) :
    ((Finset.range (n + 1)).image f).card ≤
      ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card + 1 := by
  induction n with
  | zero => rw [Finset.range_one]; simp
  | succ n ih =>
    have himg : (Finset.range (n + 1 + 1)).image f = insert (f (n+1)) ((Finset.range (n+1)).image f) := by
      nth_rewrite 1 [Finset.range_add_one (n := n+1)]
      rw [Finset.image_insert]
    have hfilt : (Finset.range (n + 1)).filter (fun i => f i ≠ f (i + 1))
        = if f n ≠ f (n+1) then insert n ((Finset.range n).filter (fun i => f i ≠ f (i + 1)))
          else (Finset.range n).filter (fun i => f i ≠ f (i + 1)) := by
      rw [Finset.range_add_one, Finset.filter_insert]
    rw [himg, hfilt]
    split_ifs with h
    · have hnot : n ∉ (Finset.range n).filter (fun i => f i ≠ f (i + 1)) := by simp
      rw [Finset.card_insert_of_notMem hnot]
      have := Finset.card_insert_le (f (n+1)) ((Finset.range (n + 1)).image f)
      omega
    · have heq : f n = f (n+1) := by tauto
      have hmem : f (n+1) ∈ (Finset.range (n + 1)).image f :=
        Finset.mem_image.mpr ⟨n, by simp, heq⟩
      rw [Finset.card_insert_of_mem hmem]
      exact ih

open Finset in
lemma cyclic_necklace_transitions_ge_two_mul_sub_one_changes {β : Type*} [DecidableEq β]
    (f : ℕ → β) (n : ℕ) :
    ((Finset.range n).image f).card ≤
      ((Finset.range (n - 1)).filter (fun i => f i ≠ f (i + 1))).card + 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have := cyclic_necklace_transitions_ge_two_mul_sub_one_changes_succ f n
    simpa using this

/-- On a cyclic necklace with r contiguous red beads and b blue beads, any allocation giving each agent at least one bead of each color has at least 2(k - 1) color transitions. -/
theorem cyclic_necklace_transitions_ge_two_mul_sub_one (m k r b : ℕ) [NeZero m]
    (hm : m = r + b) (hk : 2 ≤ k) (hr : k ≤ r) (hb : k ≤ b)
    (α : ZMod m → Fin k)
    (hred : ∀ j : Fin k, ∃ (i : ℕ) (hi : i < r), α i = j)
    (hblue : ∀ j : Fin k, ∃ (i : ℕ) (hi : r ≤ i ∧ i < m), α i = j) :
    2 * (k - 1) ≤ (Finset.univ.filter (fun i : ZMod m => α i ≠ α (i + 1))).card := by
  have hcast_inj : ∀ a c : ℕ, a < m → c < m → ((a : ZMod m) = (c : ZMod m)) → a = c := by
    intro a c ha hc h
    have hh := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hc] at hh
  let A : ℕ → Fin k := fun i => α (i : ZMod m)
  have hRimage : (Finset.range r).image A = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨i, hii, h⟩ := hred j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hii, h⟩
  have hRcard : ((Finset.range r).image A).card = k := by
    rw [hRimage, Finset.card_univ, Fintype.card_fin]
  have hred_changes : k - 1 ≤ ((Finset.range (r - 1)).filter (fun i => A i ≠ A (i + 1))).card := by
    have := cyclic_necklace_transitions_ge_two_mul_sub_one_changes A r
    rw [hRcard] at this
    omega
  let B : ℕ → Fin k := fun j => α (((r + j : ℕ)) : ZMod m)
  have hBimage : (Finset.range b).image B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨i, ⟨hri, him⟩, h⟩ := hblue j
    refine Finset.mem_image.mpr ⟨i - r, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · show α (((r + (i - r) : ℕ)) : ZMod m) = j
      rw [Nat.add_sub_cancel' hri]
      exact h
  have hBcard : ((Finset.range b).image B).card = k := by
    rw [hBimage, Finset.card_univ, Fintype.card_fin]
  have hblue_changes : k - 1 ≤ ((Finset.range (b - 1)).filter (fun j => B j ≠ B (j + 1))).card := by
    have := cyclic_necklace_transitions_ge_two_mul_sub_one_changes B b
    rw [hBcard] at this
    omega
  set T := Finset.univ.filter (fun i : ZMod m => α i ≠ α (i + 1)) with hT
  set R1 := ((Finset.range (r - 1)).filter (fun i => A i ≠ A (i + 1))).image (fun i : ℕ => (i : ZMod m)) with hR1
  set B1 := ((Finset.range (b - 1)).filter (fun j => B j ≠ B (j + 1))).image (fun j : ℕ => ((r + j : ℕ) : ZMod m)) with hB1
  have hR1T : R1 ⊆ T := by
    intro x hx
    rw [hR1] at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcast : ((i : ZMod m) + 1) = ((i + 1 : ℕ) : ZMod m) := by
      push_cast; ring
    rw [hcast]
    exact (Finset.mem_filter.mp hi).2
  have hB1T : B1 ⊆ T := by
    intro x hx
    rw [hB1] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcast : ((r + j : ℕ) : ZMod m) + 1 = ((r + j + 1 : ℕ) : ZMod m) := by
      push_cast; ring
    rw [hcast]
    have hjne : α ((r + j : ℕ) : ZMod m) ≠ α ((r + (j + 1) : ℕ) : ZMod m) := (Finset.mem_filter.mp hj).2
    have heq : r + (j + 1) = r + j + 1 := by ring
    rw [heq] at hjne
    exact hjne
  have hR1card : R1.card = ((Finset.range (r - 1)).filter (fun i => A i ≠ A (i + 1))).card := by
    rw [hR1]
    apply Finset.card_image_of_injOn
    intro a ha c hc h
    have ha' : a < m := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1; omega
    have hc' : c < m := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hc).1; omega
    exact hcast_inj a c ha' hc' h
  have hB1card : B1.card = ((Finset.range (b - 1)).filter (fun j => B j ≠ B (j + 1))).card := by
    rw [hB1]
    apply Finset.card_image_of_injOn
    intro a ha c hc h
    have ha' : r + a < m := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1; omega
    have hc' : r + c < m := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hc).1; omega
    have := hcast_inj (r + a) (r + c) ha' hc' h
    omega
  have hdisj : Disjoint R1 B1 := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    rw [hR1] at hxR
    rw [hB1] at hxB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxR
    obtain ⟨j, hj, hxj⟩ := Finset.mem_image.mp hxB
    have hi' : i < r - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' : j < b - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have him : i < m := by omega
    have hjm : r + j < m := by omega
    have := hcast_inj (r + j) i hjm him hxj
    omega
  calc 2 * (k - 1) = (k - 1) + (k - 1) := by ring
    _ ≤ R1.card + B1.card := by rw [hR1card, hB1card]; omega
    _ = (R1 ∪ B1).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ T.card := Finset.card_le_card (Finset.union_subset hR1T hB1T)
