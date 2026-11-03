import AFTD.Prelude

/-!
# digraph_oriented_two_parent_collision_limit

Topic: graphs   Node: d9d8df6cde81

Provenance: helper lemma. Multiplicity-two collision bound in the small-overlap route to OP-110.

In an oriented loopless digraph, if two vertices are dominated by both members of a displayed pair and have no common predecessor outside that pair, the two outgoing arcs from each member cannot both receive the same chosen common predecessor.
-/

theorem digraph_oriented_two_parent_collision_limit
    (α : Type) (D : Digraph α) (choose : α → α → α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hchoice : ∀ s t, D.Adj s t →
      D.Adj (choose s t) s ∧ D.Adj (choose s t) t)
    (a b u v : α)
    (hua : D.Adj u a) (hub : D.Adj u b)
    (hva : D.Adj v a) (hvb : D.Adj v b)
    (hparents : ∀ x, D.Adj x a → D.Adj x b → x = u ∨ x = v) :
    ¬ (choose u a = choose u b ∧ choose v a = choose v b) := by
  rintro ⟨hu, hv⟩
  have hpu := hchoice u a hua
  have hpu' := hchoice u b hub
  have hpb : D.Adj (choose u a) b := by rw [hu]; exact hpu'.2
  have hp : choose u a = v := by
    rcases hparents (choose u a) hpu.2 hpb with h | h
    · exact False.elim (hloop u (by simpa [h] using hpu.1))
    · exact h
  have hvu : D.Adj v u := hp ▸ hpu.1
  have hpv := hchoice v a hva
  have hpv' := hchoice v b hvb
  have hqb : D.Adj (choose v a) b := by rw [hv]; exact hpv'.2
  have hq : choose v a = u := by
    rcases hparents (choose v a) hpv.2 hqb with h | h
    · exact h
    · exact False.elim (hloop v (by simpa [h] using hpv.1))
  have huv : D.Adj u v := hq ▸ hpv.1
  exact hori u v huv hvu
