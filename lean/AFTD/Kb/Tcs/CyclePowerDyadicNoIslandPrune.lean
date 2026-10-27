import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_prune

Topic: combinatorics   Node: 1771cdd2e33c

Provenance: helper lemma. Uniform conditional structural lemmas for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The class no-island hypothesis remains explicit; its derivation from an actual optimal covering model is unresolved. No graph covering value or research advance is claimed.

Deleting middle quarters preserves the no-island property of a Boolean class.
-/

open Finset

theorem cycle_power_dyadic_no_island_prune
    (k : ℕ) (b : ℕ → Bool)
    (hshape : ∀ (a c d : ℕ), a < c → c < d → d < 2^(k+2) →
      b a = false → b c = true → b d = true) :
    ∀ (a c d : ℕ), a < c → c < d → d < 2^(k+1) →
      cycle_power_dyadic_b_lift k b a = false →
      cycle_power_dyadic_b_lift k b c = true →
      cycle_power_dyadic_b_lift k b d = true := by
  intro a c d hac hcd hd ha hc
  have hH : 2^(k+1)=2*2^k := by rw [pow_succ]; omega
  have hD : 2^(k+2)=4*2^k := by
    rw [show k+2=(k+1)+1 by omega,pow_succ,hH]; omega
  let f : ℕ → ℕ := fun i => if i < 2^k then i else i+2^(k+1)
  have he (i : ℕ) : cycle_power_dyadic_b_lift k b i = b (f i) := by
    dsimp [cycle_power_dyadic_b_lift,f]
    split_ifs <;> rfl
  rw [he] at ha hc ⊢
  apply hshape (f a) (f c) (f d)
  · dsimp [f]; split_ifs <;> omega
  · dsimp [f]; split_ifs <;> omega
  · dsimp [f]; split_ifs <;> omega
  · exact ha
  · exact hc
