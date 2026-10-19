import AFTD.Prelude

/-!
# nfa_complies_ida

Topic: automata   Node: 51f2ce549e96

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

An NFA complies with IDA if there exist distinct states p and q and a word v such that p is reachable from p by v, q is reachable from p by v, and q is reachable from q by v.
-/

/-- The IDA property of Weber and Seidl: p -v→ p -v→ q -v→ q for a single word v, read here as reachability by one word. -/
def nfa_complies_ida {α σ : Type*} (M : NFA α σ) : Prop := ∃ p q : σ, p ≠ q ∧ ∃ v : List α,
    p ∈ M.evalFrom {p} v ∧ q ∈ M.evalFrom {p} v ∧ q ∈ M.evalFrom {q} v
