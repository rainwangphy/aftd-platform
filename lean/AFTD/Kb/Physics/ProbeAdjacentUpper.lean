import AFTD.Prelude

/-!
# probe_adjacent_upper

Topic: quantum_mechanics   Node: 15b866464718

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension n : ℕ, finite probe set F : Finset ℕ, and rank j : ℕ, the upper adjacent probed rank probe_adjacent_upper n F j is the minimum of the finite set {n} ∪ {k ∈ F : k > j}.
-/

/-- Upper adjacent probed rank for an unprobed rank j, defined as min({n} ∪ {k ∈ F : k > j}). -/
def probe_adjacent_upper (n : ℕ) (F : Finset ℕ) (j : ℕ) : ℕ := (insert n (F.filter (fun k => j < k))).min' (Finset.insert_nonempty n _)
