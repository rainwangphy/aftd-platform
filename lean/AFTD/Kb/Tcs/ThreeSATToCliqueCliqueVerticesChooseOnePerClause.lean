import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVertex
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueToCliqueGraph
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.clique_vertices_choose_one_per_clause

Topic: np_completeness   Node: 6a505cebf74e

Provenance: helper lemma. TCSlib, `ThreeSATToClique.clique_vertices_choose_one_per_clause`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

One clique vertex per clause. Let $f$ be a 3-CNF formula with $m$ clauses, and let $s$ be a set of vertices of the
conflict graph of $f$. Suppose that $s$ has exactly $m$ elements and forms a clique,
meaning any two distinct vertices of $s$ are adjacent. Then for every clause index $i
\in \mathrm{Fin}\,m$ there is exactly one vertex $u \in s$ whose clause component equals
$i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- In an `m`-clique of the conflict graph, every clause index `i` is represented by *exactly one* vertex. *Proof sketch*: the clique has `m` vertices over `m` clauses; the edge condition forbids two vertices from the same clause (they would not be adjacent), so by a counting argument each clause contributes exactly one. -/
lemma ThreeSATToClique.clique_vertices_choose_one_per_clause {V : Type}
    (f : Formula3 V) (s : Finset (CliqueVertex f.length))
    (hcard : s.card = f.length) (hclique : (toCliqueGraph f).IsClique s) :
    ∀ (i : Fin f.length), ∃! u ∈ s, u.c_idx = i := by
  -- c_idx is injective on the clique: distinct clique vertices come from
  -- distinct clauses (forced by the edge condition).
  have h_inj_on : Set.InjOn (fun u : CliqueVertex f.length => u.c_idx) ↑s := by
    intro u hu v hv heq
    by_contra hne
    exact (hclique hu hv hne).1 heq
  -- Injective + same cardinality ⇒ image is everything.
  have h_image_univ : s.image (fun u => u.c_idx) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn h_inj_on, hcard, Fintype.card_fin]
  intro i
  obtain ⟨u, hu, hci⟩ := Finset.mem_image.mp (h_image_univ ▸ Finset.mem_univ i)
  refine ⟨u, ⟨hu, hci⟩, ?_⟩
  rintro v ⟨hv, hvi⟩
  exact (h_inj_on (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv)
    (hci.trans hvi.symm)).symm
