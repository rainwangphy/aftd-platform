import AFTD.Prelude

/-!
# ghz_cycle_list

Topic: graphs   Node: a9154049327a

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_radius_two

A list l is a cycle of the simple graph G when it has at least three entries, no repeated vertex, every two consecutive entries are adjacent in G, and the last entry is adjacent to the first (reading the list cyclically).
-/

/-- A cyclic vertex sequence: length ≥ 3, nodup, consecutive-adjacent, and closing edge last→first. -/
def ghz_cycle_list {V : Type*} (G : SimpleGraph V) (l : List V) : Prop := 3 ≤ l.length ∧ l.Nodup ∧ l.IsChain G.Adj ∧ ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)
