import AFTD.Prelude

/-!
# random_greedy_survival_poly

Topic: online_algorithms   Node: e67ecefc48b8

Provenance: formalization of a published result. Source: arXiv:2611.13571 Lemma 3.1

For a finite simple graph J on a finite vertex type V with decidable equality and decidable adjacency, and a vertex subset A : Finset V, the formal polynomial in ℝ[X] in the variable Y = 1 - t, recursively defined on |E(J)| by mapping each recursive polynomial on J - e and A ∪ V(e) for edges e incident to A via the zero-constant antiderivative p ↦ ∑_n (p.coeff n / (n + 1)) X^(n + 1), summing over all such incident edges e, and setting the constant term to 1 minus the evaluation of this sum at 1, so that it evaluates to 1 at 1.
-/

/-- The survival polynomial of vertex set A in graph J under random greedy matching. -/
noncomputable def random_greedy_survival_poly {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (A : Finset V) : Polynomial ℝ :=
  let incident : Finset (Sym2 V) := J.edgeFinset.filter (fun e => ∃ v ∈ A, v ∈ e)
  let poly_antideriv' (p : Polynomial ℝ) : Polynomial ℝ :=
    ∑ n ∈ p.support, Polynomial.C (p.coeff n / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)
  let step_sum := ∑ e ∈ incident.attach,
    poly_antideriv' (random_greedy_survival_poly (J.deleteEdges ↑({e.val} : Finset (Sym2 V))) (A ∪ e.val.toMultiset.toFinset))
  Polynomial.C (1 - step_sum.eval 1) + step_sum
termination_by J.edgeFinset.card
decreasing_by
  have he_inc : e.val ∈ incident := e.property
  have he_edge : e.val ∈ J.edgeFinset := (Finset.mem_filter.mp he_inc).1
  have h1 : (J.deleteEdges ↑({e.val} : Finset (Sym2 V))).edgeFinset = J.edgeFinset \ {e.val} :=
    SimpleGraph.edgeFinset_deleteEdges ({e.val} : Finset (Sym2 V))
  rw [h1, Finset.sdiff_singleton_eq_erase]
  exact Finset.card_erase_lt_of_mem he_edge
