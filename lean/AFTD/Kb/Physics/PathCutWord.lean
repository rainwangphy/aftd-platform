import AFTD.Prelude

/-!
# path_cut_word

Topic: quantum_mechanics   Node: e8f404fe88a5

Provenance: helper lemma. step towards claw_free_tree_graph_state_mmi

`path_cut_word n S` is the length-(n-1) boolean word whose j-th letter records whether the j-th edge of the path `pathGraph n` (i.e. the edge between vertex j and vertex j+1) crosses the cut `(S, Sᶜ)`. So letter j is `true` exactly when exactly one of j, j+1 lies in S.
-/

/-- Indicator word of the crossing edges of `S` along the path `pathGraph n`. -/
def path_cut_word (n : ℕ) (S : Finset (Fin n)) : List Bool := List.ofFn (fun j : Fin (n - 1) =>
    (decide ((⟨j.val, by omega⟩ : Fin n) ∈ S)) != (decide ((⟨j.val + 1, by omega⟩ : Fin n) ∈ S)))
