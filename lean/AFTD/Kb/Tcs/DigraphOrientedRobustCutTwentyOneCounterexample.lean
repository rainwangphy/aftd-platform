import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExample
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExampleCertificate
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_oriented_robust_cut_twenty_one_counterexample

Topic: graphs   Node: c47e16b45fb7

Provenance: helper lemma. Immediate corollary of the proved oriented sharp-example certificate; the related unrestricted degree-sequence criterion is https://arxiv.org/abs/2205.10826.

Let D be digraph_oriented_cut20_sharp_example on Fin 26 and B the set of vertices with value less than 20. D is oriented; B has at least seven vertices; every vertex of B has at least seven outneighbors in D; and every nonempty vertex set T in D for which every member has at least two outneighbors in T and at most two members have fewer than three outneighbors in T contains two vertex-disjoint directed cycles lying in T. Nevertheless B contains no two vertex-disjoint directed cycles and fewer than 21 arcs go from B to its complement.
-/

private instance in833_oriented_cut20_counterexample_decAdj : DecidableRel digraph_oriented_cut20_sharp_example.Adj := by
  unfold digraph_oriented_cut20_sharp_example
  infer_instance

theorem digraph_oriented_robust_cut_twenty_one_counterexample :
    let D := digraph_oriented_cut20_sharp_example
    let B : Finset (Fin 26) := Finset.univ.filter fun v => v.val < 20
    (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧ 7 ≤ B.card ∧
    (∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card) ∧
    (∀ T : Finset (Fin 26), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset (Fin 26), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 26), (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    ¬ 21 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
  have h := digraph_oriented_cut20_sharp_example_certificate
  dsimp only at h ⊢
  rcases h with ⟨ho, hd, hcut, hno, hrob⟩
  refine ⟨ho, by decide, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hd v hv]
  · intro T ht hmin hbad
    have hh := hrob T ht hmin
    omega
  · rintro ⟨c, hc, hdis⟩
    exact hno ⟨c, fun i => (hc i).2, hdis⟩
  · omega
