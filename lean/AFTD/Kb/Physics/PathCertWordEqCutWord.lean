import AFTD.Prelude
import AFTD.Kb.Physics.PathCertWord
import AFTD.Kb.Physics.PathCertMask
import AFTD.Kb.Physics.PathCutWord

/-!
# path_cert_word_eq_cut_word

Topic: quantum_mechanics   Node: 8884ec8eda3a

Provenance: helper lemma. List-index bridge from the Lean-checked word inequality to the pure-path cut-rank route for OP-827.

The Boolean edge word used by the finite-state certificate is the ordinary path cut word of the corresponding color mask.
-/

open scoped Classical

lemma cert_word_of_fn_scratch (m : ℕ) (f : Fin (m+1) → Fin 4) (j : Fin 7) :
    pathCertWord (f ⟨0, by omega⟩) (List.ofFn fun k : Fin m => f ⟨k.val+1, by omega⟩) j =
      List.ofFn (fun k : Fin m =>
        (Nat.testBit (pathCertMask j) (f ⟨k.val, by omega⟩).val !=
          Nat.testBit (pathCertMask j) (f ⟨k.val+1, by omega⟩).val)) := by
  induction m with
  | zero => simp [pathCertWord]
  | succ m ih =>
    rw [List.ofFn_succ, pathCertWord, List.ofFn_succ]
    congr 1
    simpa using ih (fun k : Fin (m+1) => f ⟨k.val+1, by omega⟩)

open scoped Classical in
theorem path_cert_word_eq_cut_word (n : ℕ) (hn : 0 < n) (color : Fin n → Fin 4) (j : Fin 7) : pathCertWord (color ⟨0, hn⟩) (List.ofFn fun k : Fin (n - 1) => color ⟨k.val + 1, by omega⟩) j = path_cut_word n (Finset.univ.filter fun v => Nat.testBit (pathCertMask j) (color v).val) := by
  cases n with
  | zero => omega
  | succ m =>
    simpa [path_cut_word] using cert_word_of_fn_scratch m color j
