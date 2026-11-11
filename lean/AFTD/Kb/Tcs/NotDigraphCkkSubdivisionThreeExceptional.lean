import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphExceptionalVerts
import AFTD.Kb.Tcs.DigraphOutDegree
import AFTD.Kb.Tcs.DigraphHasDigirthGe
import AFTD.Kb.Tcs.DigraphHasCkkSubdivision
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# not_digraph_ckk_subdivision_three_exceptional

Topic: graphs   Node: 09e25ed1fed9

Provenance: original. Related work: refutes `digraph_ckk_subdivision_three_exceptional`

The statement `digraph_ckk_subdivision_three_exceptional` is false: The statement omits any nonemptiness hypothesis on the vertex type, so it is false for the empty digraph. Take `V = PEmpty` (the empty type, available in every universe, with `Fintype` instance) and `D := ⟨fun _ _ => False⟩`. Then:
* `hloop : ∀ v, ¬ D.Adj v v` holds vacuously;
* `hmin : ∀ v, 1 ≤ digraph_out_degree D v` holds vacuously;
* `digraph_exceptional_verts D` is `Finset.filter _ Finset.univ` over the empty type, i.e. `∅`, so `(...).card = 0 ≤ 3`, giving `hexc`;
* `digraph_has_digirth_ge D g` holds vacuously: for any `c : List PEmpty`, `c` must be `[]` (length 0), contradicting the required `2 ≤ c.length`;
* but `digraph_has_ckk_subdivision D k` is `∃ u : V, ...`, which is uninhabited, hence false for every `k` (in particular for `k = 2`, where `hk : 2 ≤ 2`).

Thus every hypothesis is satisfiable while the conclusion fails, so `¬ (∀ {V} [Fintype V] (D : Digraph V) [DecidableRel D.Adj], ...)` is provable; the refutation body is machine-checked at an arbitrary universe level. (This is the only obstruction I found: for `k = 2` the small nonempty cases with digirth ≥ 4 and ≤ 3 exceptional vertices — e.g. small circulants — do exhibit the C(k,k) subdivision, consistent with the intended, nonempty statement.)
-/

open Classical in
theorem not_digraph_ckk_subdivision_three_exceptional : ¬ (∀ {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj]
    (hloop : ∀ v : V, ¬ D.Adj v v)
    (k : ℕ) (hk : 2 ≤ k)
    (hmin : ∀ v : V, 1 ≤ digraph_out_degree D v)
    (hexc : (digraph_exceptional_verts D).card ≤ 3)
    (hgirth : digraph_has_digirth_ge D (3 * (k - 1) + 1)), digraph_has_ckk_subdivision D k) := by
  intro h
  have hexc : (digraph_exceptional_verts (V := PEmpty) ⟨fun _ _ => False⟩).card ≤ 3 := by
    have : digraph_exceptional_verts (V := PEmpty) ⟨fun _ _ => False⟩ = ∅ := by
      ext x
      exact x.elim
    rw [this]
    simp
  have hgirth : digraph_has_digirth_ge (V := PEmpty) ⟨fun _ _ => False⟩ (3 * (2 - 1) + 1) := by
    intro c hc
    rcases c with _ | ⟨x, xs⟩
    · have hlen := hc.2.1
      change 2 ≤ 0 at hlen
      cases hlen
    · exact x.elim
  have hckk := h (V := PEmpty) ⟨fun _ _ => False⟩ (by intro v; exact v.elim) 2 (by norm_num) (by intro v; exact v.elim) hexc hgirth
  rcases hckk with ⟨u, -⟩
  exact u.elim
