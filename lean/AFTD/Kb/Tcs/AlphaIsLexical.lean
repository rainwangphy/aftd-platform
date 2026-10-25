import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt

/-!
# alpha_is_lexical

Topic: combinatorics   Node: e415501d0f46

Provenance: formalization of a published result. Source: Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

A nonempty positive sequence strictly larger than all its proper nonempty suffixes.
-/

def alpha_is_lexical (a : List ℕ) : Prop := a ≠ [] ∧ (∀ v ∈ a, 0 < v) ∧
    ∀ k < a.length, 0 < k → alpha_lexical_lt (a.drop k) a
