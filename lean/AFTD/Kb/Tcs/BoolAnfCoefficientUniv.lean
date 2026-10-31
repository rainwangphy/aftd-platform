import AFTD.Prelude
import AFTD.Kb.Tcs.BoolAnfCoefficient
import AFTD.Kb.Tcs.AcceptingCount

/-!
# boolAnfCoefficient_univ

Topic: circuits   Node: b85805c76ce2

Provenance: helper lemma. arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For any Boolean function f : (Fin n → Bool) → Bool on n variables, boolAnfCoefficient f Finset.univ equals decide (Odd (acceptingCount f)).
-/

/-- The top ANF coefficient equals the parity of the accepting count. -/
theorem boolAnfCoefficient_univ {n : ℕ} (f : (Fin n → Bool) → Bool) :
    boolAnfCoefficient f Finset.univ = decide (Odd (acceptingCount f)) := by
  unfold boolAnfCoefficient acceptingCount
  have h : Fintype.card { x : Fin n → Bool // f x = true ∧ ∀ j ∉ (Finset.univ : Finset (Fin n)), x j = false }
      = Fintype.card { x : Fin n → Bool // f x = true } := by
    apply Fintype.card_congr
    refine
    { toFun := fun x => ⟨x.1, x.2.1⟩
      invFun := fun x => ⟨x.1, x.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro j hj; exact absurd (Finset.mem_univ j) hj
    · intro x; exact Subtype.ext rfl
    · intro x; exact Subtype.ext rfl
  rw [h]
