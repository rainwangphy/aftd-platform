import AFTD.Prelude
import AFTD.Kb.Tcs.TernaryNae

/-!
# recursive_nae

Topic: quantum   Node: 82f057b786b0

Provenance: formalization of a published result. Source: arXiv:2611.16412 Section 5

The k-th recursive block composition F_k = NAE₃^{∘ k} of the ternary not-all-equal Boolean function on 3^k bits.
-/

/-- The k-th recursive block composition of NAE₃ on 3^k bits. -/
def recursive_nae : (k : ℕ) → (Fin (3 ^ k) → Bool) → Bool
| 0 => fun x => x ⟨0, by decide⟩
| k + 1 => fun x =>
  have h : 3 * 3 ^ k = 3 ^ (k + 1) := by ring
  let split : Fin (3 ^ (k + 1)) ≃ Fin 3 × Fin (3 ^ k) :=
    (finCongr h).symm.trans finProdFinEquiv.symm
  ternary_nae (fun i => recursive_nae k (fun j => x (split.symm (i, j))))
