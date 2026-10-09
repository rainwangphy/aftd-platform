import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount

/-!
# finset_has_no_unique_sums_sumset_of_balanced

Topic: combinatorics   Node: ce03dd066d0c

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Lemma A.2. Stated in any abelian group (the paper: F_p); B + B is written as the image of B × B under addition.

If B is a nonempty balanced finite subset of an abelian group, then its sumset B + B has no unique sums.
-/

theorem finset_has_no_unique_sums_sumset_of_balanced {G : Type*} [AddCommGroup G]
    [DecidableEq G] (B : Finset G) (hB : finset_is_midpoint_balanced B) :
    finset_has_no_unique_sums ((B ×ˢ B).image (fun x => x.1 + x.2)) := by
  classical
  set A := (B ×ˢ B).image (fun x : G × G => x.1 + x.2) with hA
  have memA : ∀ a ∈ B, ∀ b ∈ B, a + b ∈ A := fun a ha b hb =>
    Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩
  -- two different unordered pairs with the same total give two representations
  have two : ∀ p q r t : G, p ∈ A → q ∈ A → r ∈ A → t ∈ A → p + q = r + t →
      r ≠ p → r ≠ q → 2 ≤ finset_unordered_sum_rep_count A (p + q) := by
    intro p q r t hp hq hr ht hsum hrp hrq
    unfold finset_unordered_sum_rep_count
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    refine ⟨s(p, q), ?_, s(r, t), ?_, ?_⟩
    · simp [Finset.mem_filter, Finset.mk_mem_sym2_iff, hp, hq]
    · simp [Finset.mem_filter, Finset.mk_mem_sym2_iff, hr, ht, hsum]
    · intro h
      have : r ∈ s(p, q) := h ▸ Sym2.mem_mk_left r t
      rcases Sym2.mem_iff.1 this with h' | h'
      · exact hrp h'
      · exact hrq h'
  -- the repair of a pair `{x + x, x + y}`, from the balance of `x`
  have key : ∀ x ∈ B, ∀ y ∈ B, ∃ r ∈ A, ∃ t ∈ A, r + t = (x + x) + (x + y) ∧
      r ≠ x + x ∧ r ≠ x + y := by
    intro x hx y hy
    obtain ⟨u, hu, v, hv, hux, hvx, huv, hxuv⟩ := hB.2 x hx
    by_cases hu' : u + y = x + x
    · refine ⟨v + y, memA v hv y hy, u + x, memA u hu x hx, ?_, ?_, ?_⟩
      · rw [hxuv]; abel
      · intro h; exact huv (add_right_cancel (hu'.trans h.symm))
      · intro h; exact hvx (add_right_cancel h)
    · refine ⟨u + y, memA u hu y hy, v + x, memA v hv x hx, ?_, hu', ?_⟩
      · rw [hxuv]; abel
      · intro h; exact hux (add_right_cancel h)
  have fin : ∀ x ∈ B, ∀ y ∈ B, ∀ p q : G, p ∈ A → q ∈ A →
      ((p = x + x ∧ q = x + y) ∨ (p = x + y ∧ q = x + x)) →
      2 ≤ finset_unordered_sum_rep_count A (p + q) := by
    intro x hx y hy p q hp hq hpq
    obtain ⟨r, hr, t, ht, hs, hr1, hr2⟩ := key x hx y hy
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two _ _ r t hp hq hr ht hs.symm hr1 hr2
    · exact two _ _ r t hp hq hr ht (by rw [hs]; abel) hr2 hr1
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := hB.1
    obtain ⟨u, hu, v, hv, -, -, huv, -⟩ := hB.2 b hb
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    exact ⟨b + u, memA b hb u hu, b + v, memA b hb v hv, fun h => huv (add_left_cancel h)⟩
  · intro p hp q hq
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.1 hcd
    dsimp only at hp hq ⊢
    by_cases h1 : a + c ≠ a + b ∧ a + c ≠ c + d
    · exact two _ _ (a + c) (b + d) hp hq (memA a ha c hc) (memA b hb d hd) (by abel) h1.1 h1.2
    by_cases h2 : a + d ≠ a + b ∧ a + d ≠ c + d
    · exact two _ _ (a + d) (b + c) hp hq (memA a ha d hd) (memA b hb c hc) (by abel) h2.1 h2.2
    have hcb : c = b ∨ a = d := by
      by_contra hne
      push_neg at hne
      exact h1 ⟨fun h => hne.1 (add_left_cancel h),
        fun h => hne.2 (add_right_cancel (h.trans (add_comm c d)))⟩
    have hdb : d = b ∨ a = c := by
      by_contra hne
      push_neg at hne
      exact h2 ⟨fun h => hne.1 (add_left_cancel h), fun h => hne.2 (add_right_cancel h)⟩
    rcases hcb with hcb | had <;> rcases hdb with hdb | hac
    · exact fin b hb a ha _ _ hp hq (Or.inr ⟨add_comm a b, by rw [hcb, hdb]⟩)
    · have hab' : a = b := hac.trans hcb
      exact fin b hb d hd _ _ hp hq (Or.inl ⟨by rw [hab'], by rw [hcb]⟩)
    · have hab' : a = b := had.trans hdb
      exact fin b hb c hc _ _ hp hq (Or.inl ⟨by rw [hab'], by rw [hdb, add_comm]⟩)
    · exact fin a ha b hb _ _ hp hq (Or.inr ⟨rfl, by rw [← hac, ← had]⟩)
