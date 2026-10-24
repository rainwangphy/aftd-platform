import AFTD.Prelude

/-!
# finite_color_cut_signing

Topic: fair_division   Node: 3f9081f30f31

Provenance: helper lemma. Boundary-assignment helper for planar_necklace_three_agents_three_cuts; arXiv:2610.27956 Proposition 9 and its bisection step. The definition permits arbitrary signs on zero cuts.

For a finite two-colored set and a real-valued cut, if each color has even size and neither strict sign side exceeds half of that color, boundary points can be signed to give exactly half of each color to each Boolean sign.
-/

open Finset

theorem finite_color_cut_signing {X : Type*} [DecidableEq X]
    (P : Finset X) (c : X → Fin 2) (f : X → ℝ)
    (heven : ∀ j, 2 ∣ (P.filter fun p => c p = j).card)
    (hpos : ∀ j, ((P.filter fun p => c p = j).filter fun p => 0 < f p).card ≤
      (P.filter fun p => c p = j).card / 2)
    (hneg : ∀ j, ((P.filter fun p => c p = j).filter fun p => f p < 0).card ≤
      (P.filter fun p => c p = j).card / 2) :
    ∃ s : X → Bool,
      (∀ p ∈ P, (0 < f p → s p = true) ∧ (f p < 0 → s p = false)) ∧
      ∀ j, ((P.filter fun p => c p = j).filter fun p => s p = true).card =
          (P.filter fun p => c p = j).card / 2 ∧
        ((P.filter fun p => c p = j).filter fun p => s p = false).card =
          (P.filter fun p => c p = j).card / 2 := by
  classical
  let R := fun j => P.filter fun p => c p = j
  have hchoose : ∀ j, ∃ U : Finset X,
      (R j).filter (fun p => 0 < f p) ⊆ U ∧
      U ⊆ (R j).filter (fun p => 0 ≤ f p) ∧ U.card = (R j).card / 2 := by
    intro j
    have hsub : (R j).filter (fun p => 0 < f p) ⊆
        (R j).filter (fun p => 0 ≤ f p) := by
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1, le_of_lt (mem_filter.mp hp).2⟩
    have hsum : ((R j).filter fun p => f p < 0).card +
        ((R j).filter fun p => 0 ≤ f p).card = (R j).card := by
      simpa only [not_lt] using card_filter_add_card_filter_not (s := R j) (fun p => f p < 0)
    have hdiv := Nat.mod_eq_zero_of_dvd (heven j)
    have hnegj := hneg j
    change ((R j).filter fun p => f p < 0).card ≤ (R j).card / 2 at hnegj
    obtain ⟨U, hU, hU', hcard⟩ := exists_subsuperset_card_eq hsub (hpos j)
      (show (R j).card / 2 ≤ ((R j).filter fun p => 0 ≤ f p).card by omega)
    exact ⟨U, hU, hU', hcard⟩
  choose U hUpos hUnonneg hUcard using hchoose
  let s := fun p => decide (p ∈ U (c p))
  have hmem : ∀ j p, p ∈ U j → p ∈ P ∧ c p = j := by
    intro j p hp
    exact mem_filter.mp (mem_filter.mp (hUnonneg j hp)).1
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    constructor
    · intro hf
      have hpU : p ∈ U (c p) := hUpos (c p) (by simp [R, hp, hf])
      simp [s, hpU]
    · intro hf
      have hpU : p ∉ U (c p) := by
        intro hu
        have := (mem_filter.mp (hUnonneg (c p) hu)).2
        linarith
      simp [s, hpU]
  · intro j
    have htrue : (R j).filter (fun p => s p = true) = U j := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpR, hs⟩ := mem_filter.mp hp
        have hc := (mem_filter.mp hpR).2
        simpa [s, hc] using hs
      · intro hp
        obtain ⟨hpP, hpc⟩ := hmem j p hp
        simp [R, s, hpP, hpc, hp]
    have hsum := card_filter_add_card_filter_not (s := R j) (fun p => s p = true)
    have hfalse : ((R j).filter fun p => ¬ s p = true) =
        ((R j).filter fun p => s p = false) := by
      ext p
      simp
    rw [htrue, hfalse, hUcard j] at hsum
    have hdouble : (R j).card / 2 + (R j).card / 2 = (R j).card := by
      have h := Nat.div_mul_cancel (heven j)
      change (R j).card / 2 * 2 = (R j).card at h
      omega
    exact ⟨by change ((R j).filter _).card = _; rw [htrue, hUcard], by
      change ((R j).filter _).card = _
      exact Nat.add_left_cancel (hsum.trans hdouble.symm)⟩
