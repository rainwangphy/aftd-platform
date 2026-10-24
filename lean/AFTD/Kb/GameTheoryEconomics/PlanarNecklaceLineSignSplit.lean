import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine

/-!
# planar_necklace_line_sign_split

Topic: fair_division   Node: 03f3dfbe15d2

Provenance: helper lemma. step towards planar_necklace_three_agents_three_cuts

Let Q be a finite set of points coloured red (0) and blue (1), with 2a red points and 2b blue points, and let ℓ be a straight line such that each of the two strict sides of ℓ contains at most a red and at most b blue points of Q. Then the points of Q can be split into two parts, each with exactly a red and b blue points, subject to the constraint that a point strictly on the positive side of ℓ goes to the first part and a point strictly on the negative side goes to the second part (points ON the line may be assigned to either part).
-/

open Finset in
lemma planar_necklace_line_sign_split_exists_subset_on_line
    (Q : Finset (ℝ × ℝ)) (P : (ℝ × ℝ) → Prop) [DecidablePred P] (ℓ : StraightLine) (n : ℕ)
    (hn : (Q.filter (fun p => P p)).card = 2 * n)
    (hup : (Q.filter (fun p => P p ∧ 0 < ℓ.cut p)).card ≤ n)
    (hdown : (Q.filter (fun p => P p ∧ ℓ.cut p < 0)).card ≤ n) :
    ∃ T ⊆ Q.filter (fun p => P p ∧ ℓ.cut p = 0),
      T.card = n - (Q.filter (fun p => P p ∧ 0 < ℓ.cut p)).card := by
  have hd1 : Disjoint (Q.filter (fun p => P p ∧ 0 < ℓ.cut p)) (Q.filter (fun p => P p ∧ ℓ.cut p < 0)) := by
    rw [disjoint_filter]; intro p _ h1 h2; linarith
  have hd2 : Disjoint (Q.filter (fun p => P p ∧ 0 < ℓ.cut p) ∪ Q.filter (fun p => P p ∧ ℓ.cut p < 0))
                      (Q.filter (fun p => P p ∧ ℓ.cut p = 0)) := by
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_filter]; intro p _ h1 h2; linarith
    · rw [disjoint_filter]; intro p _ h1 h2; linarith
  have hsplit : Q.filter (fun p => P p) =
      Q.filter (fun p => P p ∧ 0 < ℓ.cut p) ∪
      Q.filter (fun p => P p ∧ ℓ.cut p < 0) ∪
      Q.filter (fun p => P p ∧ ℓ.cut p = 0) := by
    ext p
    simp only [mem_union, mem_filter]
    rcases lt_trichotomy (ℓ.cut p) 0 with h | h | h <;> tauto
  have hcard : (Q.filter (fun p => P p)).card =
      (Q.filter (fun p => P p ∧ 0 < ℓ.cut p)).card +
      (Q.filter (fun p => P p ∧ ℓ.cut p < 0)).card +
      (Q.filter (fun p => P p ∧ ℓ.cut p = 0)).card := by
    conv_lhs => rw [hsplit]
    rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1]
  have hle : n - (Q.filter (fun p => P p ∧ 0 < ℓ.cut p)).card ≤ (Q.filter (fun p => P p ∧ ℓ.cut p = 0)).card := by
    omega
  exact exists_subset_card_eq hle

open Finset in
lemma planar_necklace_line_sign_split_false_card
    (Q : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2) (β : (ℝ × ℝ) → Bool) (k : Fin 2) (n : ℕ)
    (htot : (Q.filter (fun p => c p = k)).card = 2 * n)
    (htrue : (Q.filter (fun p => c p = k ∧ β p = true)).card = n) :
    (Q.filter (fun p => c p = k ∧ β p = false)).card = n := by
  have h1 : Q.filter (fun p => c p = k ∧ β p = true) = (Q.filter (fun p => c p = k)).filter (fun p => β p = true) := by
    ext x; simp [and_assoc]
  have h2 : Q.filter (fun p => c p = k ∧ β p = false) = (Q.filter (fun p => c p = k)).filter (fun p => ¬ (β p = true)) := by
    ext x
    simp only [mem_filter, and_assoc]
    rw [← Bool.eq_false_eq_not_eq_true]
  rw [h1] at htrue
  rw [h2]
  have h_sum := @card_filter_add_card_filter_not _ (Q.filter (fun p => c p = k)) (fun p => β p = true) _ _
  omega

/-- Boundary-flexible signing step: if both strict sides of a line are within quota, the on-line points can be used to split the set into two exactly-balanced parts. -/
theorem planar_necklace_line_sign_split
    (Q : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2) (ℓ : StraightLine) (a b : ℕ)
    (hred : (Q.filter (fun p => c p = 0)).card = 2 * a)
    (hblue : (Q.filter (fun p => c p = 1)).card = 2 * b)
    (hup_red : (Q.filter (fun p => c p = 0 ∧ 0 < ℓ.cut p)).card ≤ a)
    (hdown_red : (Q.filter (fun p => c p = 0 ∧ ℓ.cut p < 0)).card ≤ a)
    (hup_blue : (Q.filter (fun p => c p = 1 ∧ 0 < ℓ.cut p)).card ≤ b)
    (hdown_blue : (Q.filter (fun p => c p = 1 ∧ ℓ.cut p < 0)).card ≤ b) :
    ∃ β : (ℝ × ℝ) → Bool,
      (∀ p ∈ Q, 0 < ℓ.cut p → β p = true) ∧
      (∀ p ∈ Q, ℓ.cut p < 0 → β p = false) ∧
      (Q.filter (fun p => c p = 0 ∧ β p = true)).card = a ∧
      (Q.filter (fun p => c p = 0 ∧ β p = false)).card = a ∧
      (Q.filter (fun p => c p = 1 ∧ β p = true)).card = b ∧
      (Q.filter (fun p => c p = 1 ∧ β p = false)).card = b := by
  classical
  obtain ⟨T₀, hT₀_sub, hT₀_card⟩ :=
    planar_necklace_line_sign_split_exists_subset_on_line Q (fun p => c p = 0) ℓ a hred hup_red hdown_red
  obtain ⟨T₁, hT₁_sub, hT₁_card⟩ :=
    planar_necklace_line_sign_split_exists_subset_on_line Q (fun p => c p = 1) ℓ b hblue hup_blue hdown_blue
  let β : (ℝ × ℝ) → Bool := fun p => decide (0 < ℓ.cut p ∨ p ∈ T₀ ∨ p ∈ T₁)
  have h_card_0 : (Q.filter (fun p => c p = 0 ∧ β p = true)).card = a := by
    have heq : Q.filter (fun p => c p = 0 ∧ β p = true) =
        (Q.filter (fun p => c p = 0 ∧ 0 < ℓ.cut p)) ∪ T₀ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union, decide_eq_true_iff, β]
      constructor
      · rintro ⟨hpQ, hc, hcut | hpT₀ | hpT₁⟩
        · left; exact ⟨hpQ, hc, hcut⟩
        · right; exact hpT₀
        · have h := hT₁_sub hpT₁
          simp only [Finset.mem_filter] at h
          have hc1 : c p = 1 := h.2.1
          have hne : (0 : Fin 2) ≠ 1 := by decide
          exfalso; apply hne
          rw [← hc, hc1]
      · rintro (⟨hpQ, hc, hcut⟩ | hpT₀)
        · exact ⟨hpQ, hc, Or.inl hcut⟩
        · have h := hT₀_sub hpT₀
          simp only [Finset.mem_filter] at h
          exact ⟨h.1, h.2.1, Or.inr (Or.inl hpT₀)⟩
    have hd : Disjoint (Q.filter (fun p => c p = 0 ∧ 0 < ℓ.cut p)) T₀ := by
      rw [Finset.disjoint_right]
      intro p hpT₀
      have h := hT₀_sub hpT₀
      simp only [Finset.mem_filter] at h ⊢
      intro ⟨_, _, hcut⟩
      have : ℓ.cut p = 0 := h.2.2
      linarith
    rw [heq, Finset.card_union_of_disjoint hd, hT₀_card]
    omega
  have h_card_1 : (Q.filter (fun p => c p = 1 ∧ β p = true)).card = b := by
    have heq : Q.filter (fun p => c p = 1 ∧ β p = true) =
        (Q.filter (fun p => c p = 1 ∧ 0 < ℓ.cut p)) ∪ T₁ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union, decide_eq_true_iff, β]
      constructor
      · rintro ⟨hpQ, hc, hcut | hpT₀ | hpT₁⟩
        · left; exact ⟨hpQ, hc, hcut⟩
        · have h := hT₀_sub hpT₀
          simp only [Finset.mem_filter] at h
          have hc0 : c p = 0 := h.2.1
          have hne : (1 : Fin 2) ≠ 0 := by decide
          exfalso; apply hne
          rw [← hc, hc0]
        · right; exact hpT₁
      · rintro (⟨hpQ, hc, hcut⟩ | hpT₁)
        · exact ⟨hpQ, hc, Or.inl hcut⟩
        · have h := hT₁_sub hpT₁
          simp only [Finset.mem_filter] at h
          exact ⟨h.1, h.2.1, Or.inr (Or.inr hpT₁)⟩
    have hd : Disjoint (Q.filter (fun p => c p = 1 ∧ 0 < ℓ.cut p)) T₁ := by
      rw [Finset.disjoint_right]
      intro p hpT₁
      have h := hT₁_sub hpT₁
      simp only [Finset.mem_filter] at h ⊢
      intro ⟨_, _, hcut⟩
      have : ℓ.cut p = 0 := h.2.2
      linarith
    rw [heq, Finset.card_union_of_disjoint hd, hT₁_card]
    omega
  refine ⟨β, ?_, ?_, h_card_0, ?_, h_card_1, ?_⟩
  · intro p _ hcut
    simp only [β, decide_eq_true_iff]
    exact Or.inl hcut
  · intro p _ hcut
    simp only [β, decide_eq_false_iff_not]
    rintro (h | hpT₀ | hpT₁)
    · linarith
    · have h := hT₀_sub hpT₀
      simp only [Finset.mem_filter] at h
      have : ℓ.cut p = 0 := h.2.2
      linarith
    · have h := hT₁_sub hpT₁
      simp only [Finset.mem_filter] at h
      have : ℓ.cut p = 0 := h.2.2
      linarith
  · exact planar_necklace_line_sign_split_false_card Q c β 0 a hred h_card_0
  · exact planar_necklace_line_sign_split_false_card Q c β 1 b hblue h_card_1
