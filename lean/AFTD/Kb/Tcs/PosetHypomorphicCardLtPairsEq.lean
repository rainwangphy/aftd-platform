import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHypomorphic

/-!
# poset_hypomorphic_card_lt_pairs_eq

Topic: combinatorics   Node: 781a463c5d01

Provenance: formalization of a published result. Source: The standard counting lemma of reconstruction theory, applied to comparabilities; serves the height-one reconstruction question of arXiv:2610.12690 (Reconstruction of Finite Posets of Width Three), Sec. 9. The bound |P| ≥ 3 is needed: the 2-chain and the 2-antichain have the same deck.

The number of comparable pairs is reconstructible: if finite ordered sets P and Q with |P| ≥ 3 have the same deck, they have the same number of pairs a < b. (Each such pair survives in exactly |P| − 2 of the cards, so the count is the sum over the deck divided by |P| − 2.)
-/

theorem poset_hypomorphic_card_lt_pairs_eq (P Q : Type) [Fintype P] [Fintype Q]
    [PartialOrder P] [PartialOrder Q] [DecidableRel ((· < ·) : P → P → Prop)]
    [DecidableRel ((· < ·) : Q → Q → Prop)] (hn : 3 ≤ Fintype.card P)
    (h : poset_hypomorphic P Q) :
    (Finset.univ.filter (fun p : P × P => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Q × Q => p.1 < p.2)).card := by
  classical
  obtain ⟨σ, hσ⟩ := h
  have hcard : Fintype.card Q = Fintype.card P := (Fintype.card_congr σ).symm
  have sumP : ∀ (R : Type) [Fintype R] [PartialOrder R] [DecidableRel ((· < ·) : R → R → Prop)],
      ∑ x : R, (Finset.univ.filter (fun p : R × R => p.1 < p.2 ∧ p.1 ≠ x ∧ p.2 ≠ x)).card =
        (Fintype.card R - 2) * (Finset.univ.filter (fun p : R × R => p.1 < p.2)).card := by
    intro R _ _ _
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 < p.2
    · simp only [hp, true_and, if_true, mul_one]
      rw [← Finset.card_filter]
      have hfil : Finset.univ.filter (fun x => p.1 ≠ x ∧ p.2 ≠ x) =
          (Finset.univ.erase p.1).erase p.2 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨fun h' => h2 h'.symm, fun h' => h1 h'.symm⟩
        · rintro ⟨h1, h2⟩; exact ⟨fun h' => h2 h'.symm, fun h' => h1 h'.symm⟩
      rw [hfil, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      · omega
      · exact Finset.mem_erase.mpr ⟨hp.ne', Finset.mem_univ _⟩
    · simp [hp]
  have subcount : ∀ (R : Type) [Fintype R] [PartialOrder R]
      [DecidableRel ((· < ·) : R → R → Prop)] (x : R),
      (Finset.univ.filter (fun p : {y : R // y ≠ x} × {y : R // y ≠ x} => p.1 < p.2)).card =
        (Finset.univ.filter (fun p : R × R => p.1 < p.2 ∧ p.1 ≠ x ∧ p.2 ≠ x)).card := by
    intro R _ _ _ x
    apply Finset.card_bij (fun p _ => ((p.1 : R), (p.2 : R)))
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
      exact ⟨hab, a.2, b.2⟩
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ hh
      simp only [Prod.mk.injEq] at hh
      rw [Subtype.ext hh.1, Subtype.ext hh.2]
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
      refine ⟨(⟨a, hab.2.1⟩, ⟨b, hab.2.2⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hab.1
  have isoc : ∀ x : P,
      (Finset.univ.filter (fun p : {y : P // y ≠ x} × {y : P // y ≠ x} => p.1 < p.2)).card =
        (Finset.univ.filter
          (fun p : {y : Q // y ≠ σ x} × {y : Q // y ≠ σ x} => p.1 < p.2)).card := by
    intro x
    obtain ⟨e⟩ := hσ x
    apply Finset.card_bij (fun p _ => (e p.1, e p.2))
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
      exact e.lt_iff_lt.mpr hab
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ hh
      simp only [Prod.mk.injEq] at hh
      rw [e.injective hh.1, e.injective hh.2]
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
      refine ⟨(e.symm a, e.symm b), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact e.symm.lt_iff_lt.mpr hab
  have hsum : ∑ x : P, (Finset.univ.filter (fun p : P × P => p.1 < p.2 ∧ p.1 ≠ x ∧ p.2 ≠ x)).card =
      ∑ y : Q, (Finset.univ.filter (fun p : Q × Q => p.1 < p.2 ∧ p.1 ≠ y ∧ p.2 ≠ y)).card := by
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro x _
    rw [← subcount P x, ← subcount Q (σ x), isoc x]
  rw [sumP P, sumP Q, hcard] at hsum
  exact Nat.eq_of_mul_eq_mul_left (by omega) hsum
