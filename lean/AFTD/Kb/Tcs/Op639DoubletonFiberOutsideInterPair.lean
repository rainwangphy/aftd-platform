import AFTD.Prelude
import AFTD.Kb.Tcs.Op639DisjointTraceFibersOutsideInter

/-!
# op_639_doubleton_fiber_outside_inter_pair

Topic: combinatorics   Node: b3a0d9dce3eb

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

Let F be intersecting, T a set, S a 2-element subset of T, and e in F with e ∩ T = S. If x1, x2 in T \ S have private singleton edges e1, e2 with e1 ∩ T = {x1} and e2 ∩ T = {x2}, then e \ T intersects both e1 \ T and e2 \ T.
-/

/-- For any 2-element trace S in T and any private singleton edges e1, e2 for elements of T \ S, every edge in the fiber of S intersects both e1 \ T and e2 \ T outside T. -/
theorem op_639_doubleton_fiber_outside_inter_pair
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hinter : (F : Set (Finset V)).Intersecting)
    (T : Finset V) (S : Finset V)
    (e e1 e2 : Finset V) (he : e ∈ F) (he1 : e1 ∈ F) (he2 : e2 ∈ F)
    (heS : e ∩ T = S) (x1 x2 : V)
    (hx1 : x1 ∈ T \ S) (hx2 : x2 ∈ T \ S)
    (he1x : e1 ∩ T = {x1}) (he2x : e2 ∩ T = {x2}) :
    ¬Disjoint (e \ T) (e1 \ T) ∧ ¬Disjoint (e \ T) (e2 \ T) := by
  have hdisj1 : Disjoint (e ∩ T) (e1 ∩ T) := by
    rw [heS, he1x]
    rw [Finset.disjoint_singleton_right]
    exact (Finset.mem_sdiff.mp hx1).2
  have hdisj2 : Disjoint (e ∩ T) (e2 ∩ T) := by
    rw [heS, he2x]
    rw [Finset.disjoint_singleton_right]
    exact (Finset.mem_sdiff.mp hx2).2
  exact ⟨op_639_disjoint_trace_fibers_outside_inter F hinter T e e1 he he1 hdisj1,
         op_639_disjoint_trace_fibers_outside_inter F hinter T e e2 he he2 hdisj2⟩
