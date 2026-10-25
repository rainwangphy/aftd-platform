import AFTD.Prelude

/-!
# fin_six_three_consecutive_not_injective

Topic: fair_division   Node: 6dc3d1dc51de

Provenance: helper lemma. step towards planar_necklace_three_agents_two_cuts

If a function v : {0,...,5} → Bool × Bool has convex fibres (v i = v k forces v j = v i for i ≤ j ≤ k) and separates the two colours in the sense that equal values at two indices force those indices to lie on the same side of the cut 3, then v cannot be injective on three consecutive indices: any a, b, c with a ≠ b, b ≠ c, a ≠ c and v a = v b = v c is impossible. Equivalently, of any three indices at least two have equal values, and if those two straddle 3 they coincide, so three consecutive indices yield at most two distinct values.
-/

/-- Three consecutive indices cannot all carry pairwise distinct colour-mixed class values. -/
theorem fin_six_three_consecutive_not_injective (v : Fin 6 → Bool × Bool)
    (hsep : ∀ i j : Fin 6, v i = v j → ((i : ℕ) < 3 ↔ (j : ℕ) < 3) → i = j) :
    ∀ a b c : Fin 6, a ≠ b → b ≠ c → a ≠ c → v a = v b → v b = v c → False := by
  intro a b c hab hbc hac h1 h2
  by_cases ha : (a : ℕ) < 3
  · by_cases hb : (b : ℕ) < 3
    · exact hab (hsep a b h1 ⟨fun _ => hb, fun _ => ha⟩)
    · by_cases hc : (c : ℕ) < 3
      · exact hac (hsep a c (h1.trans h2) ⟨fun _ => hc, fun _ => ha⟩)
      · exact hbc (hsep b c h2 ⟨fun h => (hb h).elim, fun h => (hc h).elim⟩)
  · by_cases hb : (b : ℕ) < 3
    · by_cases hc : (c : ℕ) < 3
      · exact hbc (hsep b c h2 ⟨fun _ => hc, fun _ => hb⟩)
      · exact hac (hsep a c (h1.trans h2) ⟨fun h => (ha h).elim, fun h => (hc h).elim⟩)
    · exact hab (hsep a b h1 ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩)
