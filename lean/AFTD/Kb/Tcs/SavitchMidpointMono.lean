import AFTD.Prelude
import AFTD.Kb.Tcs.SavitchMidpoint

/-!
# savitch_midpoint_mono

Topic: space_complexity   Node: 2f85621d0539

Provenance: helper lemma. Savitch 1970, Section 2; Sipser, Theorem 8.5

The Savitch midpoint reachability relation is monotone in the recursion depth: for any relation r on V, any depth k, and any vertices u and v, if SavitchMidpoint r k u v holds, then SavitchMidpoint r (k + 1) u v also holds.
-/

lemma savitch_midpoint_mono_refl {V : Type*} (r : V → V → Prop) (k : ℕ) (v : V) :
    SavitchMidpoint r k v v := by
  induction k with
  | zero =>
    dsimp [SavitchMidpoint]
    exact Or.inl rfl
  | succ k ih =>
    dsimp [SavitchMidpoint]
    exact ⟨v, ih, ih⟩

/-- Savitch midpoint reachability is monotone in recursion depth: R_k(r, u, v) implies R_{k+1}(r, u, v). -/
theorem savitch_midpoint_mono {V : Type*} (r : V → V → Prop) (k : ℕ) {u v : V}
    (h : SavitchMidpoint r k u v) : SavitchMidpoint r (k + 1) u v := by
  dsimp [SavitchMidpoint]
  exact ⟨v, h, savitch_midpoint_mono_refl r k v⟩
