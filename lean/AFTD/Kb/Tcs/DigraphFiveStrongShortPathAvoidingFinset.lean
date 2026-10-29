import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_five_strong_short_path_avoiding_finset

Topic: graphs   Node: 21ff472fefcd

Provenance: helper lemma. step towards digraph_five_strong_co_bipartite_unilaterally_two_linked

Let D be 5-strong, A₀ a set of at most 2 vertices and T a set of fewer than 3 vertices. Then any two distinct vertices outside T ∪ A₀ are joined by a directed path avoiding T ∪ A₀. This is 5-strongness applied to the set T ∪ A₀, which has fewer than 5 vertices.
-/

/-- Five-strongness, applied to T ∪ A₀, gives paths avoiding both T and a set A₀ of at most two vertices. -/
theorem digraph_five_strong_short_path_avoiding_finset {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) (hstrong : digraph_is_k_strong D 5) (A₀ : Finset V) (hA : A₀.card ≤ 2)
    (T : Finset V) (hT : T.card < 3) {u v : V} (huT : u ∉ T) (hvT : v ∉ T)
    (huA : u ∉ A₀) (hvA : v ∉ A₀) (huv : u ≠ v) :
    ∃ p : List V, digraph_is_directed_path D p u v ∧ (∀ x ∈ p, x ∉ T) ∧ ∀ x ∈ p, x ∉ A₀ := by
  have hcard : (T ∪ A₀).card < 5 := by
    have h := Finset.card_union_le T A₀
    omega
  have hu : u ∉ T ∪ A₀ := by simp [huT, huA]
  have hv : v ∉ T ∪ A₀ := by simp [hvT, hvA]
  obtain ⟨p, hp1, hp2⟩ := hstrong.2 (T ∪ A₀) hcard u v hu hv huv
  have hp2' : ∀ x ∈ p, x ∉ T ∧ x ∉ A₀ := by
    intro x hx
    simpa [Finset.notMem_union] using hp2 x hx
  exact ⟨p, hp1, fun x hx => (hp2' x hx).1, fun x hx => (hp2' x hx).2⟩
