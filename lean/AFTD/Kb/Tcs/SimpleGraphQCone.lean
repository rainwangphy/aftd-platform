import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphQ
import AFTD.Kb.Tcs.SimpleGraphIsCone

/-!
# simple_graph_q_cone

Topic: graphs   Node: aa2c6d61bb1d

Provenance: helper lemma. arXiv:2611.14430, Lemma 4.3

If a finite simple graph $G$ is a cone, then $q(G) = 0$.
-/

private lemma simple_graph_q_cone_insert_isClique {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a : V}
    (ha : G.IsUniversal a) {s : Finset V} (hs : G.IsClique (↑s : Set V)) :
    G.IsClique (↑(insert a s) : Set V) := by
  rw [Finset.coe_insert]
  exact SimpleGraph.isClique_insert.mpr ⟨hs, fun b hb hab => ha hab⟩

private lemma simple_graph_q_cone_erase_isClique {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a : V}
    {s : Finset V} (hs : G.IsClique (↑s : Set V)) :
    G.IsClique (↑(s.erase a) : Set V) :=
  hs.subset (fun _ hx => Finset.mem_of_mem_erase hx)

private lemma simple_graph_q_cone_neg_one_pow_succ_add (m : ℕ) : (-1 : ℤ) ^ (m + 1) + (-1 : ℤ) ^ m = 0 := by
  rw [pow_succ]; ring

private lemma simple_graph_q_cone_neg_one_pow_add_succ (m : ℕ) : (-1 : ℤ) ^ m + (-1 : ℤ) ^ (m + 1) = 0 := by
  rw [pow_succ]; ring

private lemma simple_graph_q_cone_pair_involutive {V : Type*} [DecidableEq V] (a : V) (s : Finset V) :
    (if a ∈ (if a ∈ s then s.erase a else insert a s) then
        (if a ∈ s then s.erase a else insert a s).erase a
      else insert a (if a ∈ s then s.erase a else insert a s)) = s := by
  by_cases h : a ∈ s
  · rw [if_pos h, if_neg (Finset.notMem_erase a s), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self a s), Finset.erase_insert h]

/-- A cone has q = 0. -/
theorem simple_graph_q_cone {V : Type*} [Fintype V] (G : SimpleGraph V) (hcone : simple_graph_is_cone G) :
    simple_graph_q G = 0 := by
  classical
  obtain ⟨_, a, ha⟩ := hcone
  simp only [simple_graph_q, simple_graph_clique_polynomial]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  set F : Finset (Finset V) := Finset.univ.filter (fun s : Finset V => G.IsClique (↑s : Set V)) with hF
  have hterm : ∀ t, (∑ s ∈ G.cliqueFinset t, (-1 : ℤ) ^ s.card) = ((G.cliqueFinset t).card : ℤ) * (-1 : ℤ)^t := by
    intro t
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [show s.card = t from (SimpleGraph.isNClique_iff G |>.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs)).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdisj : ((Finset.range (Fintype.card V + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun t => G.cliqueFinset t) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i _ j _ hne
    obtain ⟨s, hs⟩ := hne
    rw [Finset.mem_inter] at hs
    obtain ⟨hsi, hsj⟩ := hs
    have hi : s.card = i := (SimpleGraph.isNClique_iff G |>.mp (SimpleGraph.mem_cliqueFinset_iff.mp hsi)).2
    have hj : s.card = j := (SimpleGraph.isNClique_iff G |>.mp (SimpleGraph.mem_cliqueFinset_iff.mp hsj)).2
    exact hi.symm.trans hj
  have hbiUnion : (Finset.range (Fintype.card V + 1)).biUnion (fun t => G.cliqueFinset t) = F := by
    ext s
    simp only [Finset.mem_biUnion, Finset.mem_range, hF, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, _, ht⟩
      exact (SimpleGraph.mem_cliqueFinset_iff.mp ht).isClique
    · intro hcl
      exact ⟨s.card, Nat.lt_succ_of_le (Finset.card_le_univ s),
        SimpleGraph.mem_cliqueFinset_iff.mpr ((SimpleGraph.isNClique_iff G).mpr ⟨hcl, rfl⟩)⟩
  have hEq1 : ∑ t ∈ Finset.range (Fintype.card V + 1), ((G.cliqueFinset t).card : ℤ) * (-1 : ℤ)^t
      = ∑ s ∈ F, (-1 : ℤ) ^ s.card := by
    calc ∑ t ∈ Finset.range (Fintype.card V + 1), ((G.cliqueFinset t).card : ℤ) * (-1 : ℤ)^t
        = ∑ t ∈ Finset.range (Fintype.card V + 1), ∑ s ∈ G.cliqueFinset t, (-1 : ℤ) ^ s.card :=
          Finset.sum_congr rfl (fun t _ => (hterm t).symm)
      _ = ∑ s ∈ (Finset.range (Fintype.card V + 1)).biUnion (fun t => G.cliqueFinset t), (-1 : ℤ) ^ s.card :=
          (Finset.sum_biUnion hdisj).symm
      _ = ∑ s ∈ F, (-1 : ℤ) ^ s.card := by rw [hbiUnion]
  rw [hEq1]
  refine Finset.sum_involution (f := fun s : Finset V => (-1 : ℤ) ^ s.card)
    (g := fun s _ => if a ∈ s then s.erase a else insert a s) ?_ ?_ ?_ ?_
  · intro s hs
    by_cases h : a ∈ s
    · rw [if_pos h]
      have hc : s.card = (s.erase a).card + 1 := (Finset.card_erase_add_one h).symm
      rw [hc]
      exact simple_graph_q_cone_neg_one_pow_succ_add _
    · rw [if_neg h]
      rw [Finset.card_insert_of_notMem h]
      exact simple_graph_q_cone_neg_one_pow_add_succ _
  · intro s hs hfne hg
    by_cases h : a ∈ s
    · have hnot : a ∉ (if a ∈ s then s.erase a else insert a s) := by
        rw [if_pos h]; exact Finset.notMem_erase a s
      rw [hg] at hnot
      exact hnot h
    · have hmem : a ∈ (if a ∈ s then s.erase a else insert a s) := by
        rw [if_neg h]; exact Finset.mem_insert_self a s
      rw [hg] at hmem
      exact h hmem
  · intro s hs
    have hcl : G.IsClique (↑s : Set V) := by
      simpa only [hF, Finset.mem_filter, Finset.mem_univ, true_and] using hs
    rw [hF]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : a ∈ s
    · rw [if_pos h]
      exact simple_graph_q_cone_erase_isClique hcl
    · rw [if_neg h]
      exact simple_graph_q_cone_insert_isClique ha hcl
  · intro s hs
    exact simple_graph_q_cone_pair_involutive a s
