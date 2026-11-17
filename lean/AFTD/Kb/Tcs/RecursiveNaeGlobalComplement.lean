import AFTD.Prelude
import AFTD.Kb.Tcs.RecursiveNae
import AFTD.Kb.Tcs.TernaryNae

/-!
# recursive_nae_global_complement

Topic: quantum   Node: 1f3b54a324a0

Provenance: helper lemma. The recursive function of arXiv:2611.16412 Section 5; supporting the odd-query clean-phase reduction for OP-1638.

For every positive depth k, complementing every input bit leaves the recursive ternary not-all-equal function unchanged.
-/

lemma ternary_nae_complement (x : Fin 3 → Bool) :
    ternary_nae (fun i => !(x i)) = ternary_nae x := by
  unfold ternary_nae
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> simp [hx0, hx1, hx2]

/-- Recursive ternary not-all-equal is invariant under global input complement at positive depth. -/
theorem recursive_nae_global_complement (k : ℕ) : ∀ (hk : 1 ≤ k)
    (x : Fin (3 ^ k) → Bool),
    recursive_nae k (fun i => !(x i)) = recursive_nae k x := by
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk x
      let split : Fin (3 ^ (k + 1)) ≃ Fin 3 × Fin (3 ^ k) :=
        (finCongr (by ring : 3 * 3 ^ k = 3 ^ (k + 1))).symm.trans finProdFinEquiv.symm
      change ternary_nae (fun i => recursive_nae k (fun j => !(x (split.symm (i,j))))) =
        ternary_nae (fun i => recursive_nae k (fun j => x (split.symm (i,j))))
      cases k with
      | zero => exact ternary_nae_complement _
      | succ k =>
          congr 1
          funext i
          exact ih (by omega) (fun j => x (split.symm (i,j)))
