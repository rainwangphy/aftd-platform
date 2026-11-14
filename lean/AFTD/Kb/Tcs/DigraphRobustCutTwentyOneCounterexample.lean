import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCut20SharpExample
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphCut20SharpExampleCertificate

/-!
# digraph_robust_cut_twenty_one_counterexample

Topic: graphs   Node: d2df7f6ca040

Provenance: original. Related work: Adaptation of the two-cycle extremal construction in https://arxiv.org/abs/2205.10826, Figure 3.2, with sink vertices; experiments 26197 and 26198.

Let D be digraph_cut20_sharp_example on Fin 20 and let B be the vertices with value below 13. The set B has at least seven vertices, each vertex in B has outdegree at least seven, and no two vertex-disjoint directed cycles both lie in B. For every nonempty subset T, if every vertex of T has at least two outneighbors in T and at most two vertices of T have fewer than three outneighbors in T, then T contains two vertex-disjoint directed cycles. Fewer than 21 arcs go from B to its complement.
-/

private instance in833_cut20_counterexample_decAdj : DecidableRel digraph_cut20_sharp_example.Adj := by
  unfold digraph_cut20_sharp_example
  infer_instance

theorem digraph_robust_cut_twenty_one_counterexample :
    let D := digraph_cut20_sharp_example
    let B : Finset (Fin 20) := Finset.univ.filter fun v => v.val < 13
    7 ≤ B.card ∧
    (∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card) ∧
    (∀ T : Finset (Fin 20), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset (Fin 20), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 20),
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    ¬ 21 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
  have h := digraph_cut20_sharp_example_certificate
  dsimp only at h ⊢
  rcases h with ⟨hd,hcut,hno,hrob⟩
  refine ⟨by decide, ?_, ?_, hno, ?_⟩
  · intro v hv
    rw [hd v hv]
  · intro T ht hmin hbad
    have hh := hrob T ht hmin
    omega
  · omega
