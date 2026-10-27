import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection

/-!
# cycle_power_dyadic_outer_projection_no_island

Topic: combinatorics   Node: 096c093f2b77

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

Direct outer projection preserves no-island shape.
-/

open Finset

theorem cycle_power_dyadic_outer_projection_no_island
    (M r : ℕ) (hr : r ≤ M) (b : ℕ → Bool)
    (hshape : ∀ a c d : ℕ, a < c → c < d → d < 2^(M+1) →
      b a = false → b c = true → b d = true) :
    ∀ a c d : ℕ, a < c → c < d → d < 2^(r+1) →
      cycle_power_dyadic_outer_projection (M+1) r b a = false →
      cycle_power_dyadic_outer_projection (M+1) r b c = true →
      cycle_power_dyadic_outer_projection (M+1) r b d = true := by
  have hp : 2^(r+1) ≤ 2^(M+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hH : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
  let f : ℕ → ℕ := fun i => if i < 2^r then i else i+2^(M+1)-2^(r+1)
  have he (i : ℕ) : cycle_power_dyadic_outer_projection (M+1) r b i = b (f i) := by
    dsimp [cycle_power_dyadic_outer_projection,f]
    split_ifs <;> rfl
  intro a c d hac hcd hd ha hc
  rw [he] at ha hc ⊢
  apply hshape (f a) (f c) (f d)
  · dsimp [f]; split_ifs <;> omega
  · dsimp [f]; split_ifs <;> omega
  · dsimp [f]; split_ifs <;> omega
  · exact ha
  · exact hc
