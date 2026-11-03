import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphWeightedCenterStrict54Graph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorDoubleEdges
import AFTD.Kb.Tcs.DigraphStrict54NonadjMaskSound
import AFTD.Kb.Tcs.DigraphStrict54OutMaskDoubleCount
import AFTD.Kb.Tcs.DigraphStrict54NonadjMaskFour
import AFTD.Kb.Tcs.DigraphStrict54AdjIffOutMask
import AFTD.Kb.Tcs.DigraphStrict54OutMaskPairCount
import AFTD.Kb.Tcs.DigraphStrict54OutMask
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.DigraphStrict54OutMaskFacts
import AFTD.Kb.Tcs.DigraphStrict54NonadjMask
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_weighted_center_strict54_certificate

Topic: graphs   Node: 88c80a3d993c

Provenance: helper lemma. Strictness witness for the weighted center route; experiments 13477 and 13478.

The displayed 54-vertex graph is loopless, oriented, triangle-free and arc-dominated, has minimum outdegree seven and auxiliary independence at most three, and has overlap 18 with exactly 15 common-predecessor pairs of multiplicity two.
-/

private instance in516_strict54_adj : DecidableRel digraph_weighted_center_strict54_graph.Adj := by
  intro u v
  unfold digraph_weighted_center_strict54_graph
  infer_instance
private instance in516_strict54_common_adj : DecidableRel (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

private theorem in522_edge_card {n : ℕ} (G : SimpleGraph (Fin n)) [Fintype G.edgeSet]
    (P : Sym2 (Fin n) → Prop) [DecidablePred P] [DecidableRel G.Adj] :
    (G.edgeFinset.filter P).card =
      ((Finset.univ : Finset (Fin n × Fin n)).filter fun x => x.1 < x.2 ∧ G.Adj x.1 x.2 ∧ P s(x.1, x.2)).card := by
  symm
  apply Finset.card_bij (fun x _ => s(x.1, x.2))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hx.2.1, hx.2.2⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rcases Sym2.eq_iff.mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have := hx.1; have := hy.1
      rw [h1, h2] at hx
      exact absurd hx.1 (lt_asymm hy.1)
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, hP⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases lt_or_gt_of_ne (G.ne_of_adj he) with h | h
      · exact ⟨(x, y), by simp [h, he, hP], rfl⟩
      · refine ⟨(y, x), ?_, Sym2.eq_swap⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, G.adj_symm he, by rw [Sym2.eq_swap]; exact hP⟩

theorem digraph_weighted_center_strict54_certificate :
    (∀ u, ¬ digraph_weighted_center_strict54_graph.Adj u u) ∧
    (∀ u v, digraph_weighted_center_strict54_graph.Adj u v →
      ¬ digraph_weighted_center_strict54_graph.Adj v u) ∧
    (∀ u v w, digraph_weighted_center_strict54_graph.Adj u v →
      digraph_weighted_center_strict54_graph.Adj v w →
      ¬ digraph_weighted_center_strict54_graph.Adj w u) ∧
    (∀ u v, digraph_weighted_center_strict54_graph.Adj u v → ∃ p,
      digraph_weighted_center_strict54_graph.Adj p u ∧
      digraph_weighted_center_strict54_graph.Adj p v) ∧
    (∀ u, 7 ≤ (Finset.univ.filter fun v => digraph_weighted_center_strict54_graph.Adj u v).card) ∧
    (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).IndepSetFree 4 ∧
    ((∑ v : Fin 54, Nat.choose (Finset.univ.filter fun w =>
      digraph_weighted_center_strict54_graph.Adj v w).card 2) -
        (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).edgeFinset.card) = 18 ∧
    digraph_common_predecessor_double_edges (Fin 54) digraph_weighted_center_strict54_graph = 15 := by
  have hA := digraph_strict54_adj_iff_out_mask
  obtain ⟨hloop, hor, htri, hdom, hdeg, hch⟩ := digraph_strict54_out_mask_facts
  have hfilt : ∀ u : Fin 54, (Finset.univ.filter fun v => digraph_weighted_center_strict54_graph.Adj u v) =
      Finset.univ.filter fun v : Fin 54 => (digraph_strict54_out_mask u.val).testBit v.val = true :=
    fun u => Finset.filter_congr fun v _ => hA u v
  have hJ : ∀ a b : Fin 54, (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).Adj a b ↔
      a ≠ b ∧ ∃ w : Fin 54, (digraph_strict54_out_mask w.val).testBit a.val = true ∧ (digraph_strict54_out_mask w.val).testBit b.val = true := by
    intro a b
    change (a ≠ b ∧ ∃ w, digraph_weighted_center_strict54_graph.Adj w a ∧ digraph_weighted_center_strict54_graph.Adj w b) ↔ _
    simp only [hA]
  have hJbit : ∀ a b : Fin 54, a ≠ b →
      ¬ (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).Adj a b →
      (digraph_strict54_nonadj_mask a.val).testBit b.val = true := by
    intro a b hab hn
    by_contra hb
    rw [Bool.not_eq_true] at hb
    exact hn ((hJ a b).mpr ⟨hab, digraph_strict54_nonadj_mask_sound a b hab hb⟩)
  have hEdges : (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph).edgeFinset.card = 1144 := by
    have h := in522_edge_card (digraph_common_predecessor_graph digraph_weighted_center_strict54_graph) (fun _ => True)
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
    rw [h]
    refine (congrArg Finset.card ?_).trans digraph_strict54_out_mask_pair_count
    apply Finset.filter_congr
    intro x _
    rw [hJ]
    exact ⟨fun h => ⟨h.1, h.2.1.2⟩, fun h => ⟨h.1, ⟨ne_of_lt h.1, h.2⟩, trivial⟩⟩
  refine ⟨fun u h => ?_, fun u v h1 h2 => ?_, fun u v w h1 h2 h3 => ?_, fun u v h => ?_, fun u => ?_, ?_, ?_, ?_⟩
  · rw [hA, hloop u] at h; exact Bool.false_ne_true h
  · rw [hA] at h1 h2; rw [hor u v h1] at h2; exact Bool.false_ne_true h2
  · rw [hA] at h1 h2 h3; rw [htri u v h1 w h2] at h3; exact Bool.false_ne_true h3
  · rw [hA] at h
    obtain ⟨p, hp1, hp2⟩ := hdom u v h
    exact ⟨p, (hA p u).mpr hp1, (hA p v).mpr hp2⟩
  · rw [hfilt]; exact hdeg u
  · intro t ht
    obtain ⟨hind, hcard⟩ := ht
    obtain ⟨a, s, ha, rfl, hs⟩ := Finset.card_eq_succ.mp hcard
    obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    obtain ⟨hab, hac, had⟩ := ha
    have hn : ∀ x y : Fin 54, x ∈ ({a, b, c, d} : Finset (Fin 54)) → y ∈ ({a, b, c, d} : Finset (Fin 54)) →
        x ≠ y → (digraph_strict54_nonadj_mask x.val).testBit y.val = true := by
      intro x y hx hy hxy
      exact hJbit x y hxy (hind (by exact_mod_cast hx) (by exact_mod_cast hy) hxy)
    have h0 := digraph_strict54_nonadj_mask_four a b c (hn a b (by simp) (by simp) hab) (hn a c (by simp) (by simp) hac)
      (hn b c (by simp) (by simp) hbc)
    have h1 : (digraph_strict54_nonadj_mask a.val &&& digraph_strict54_nonadj_mask b.val &&& digraph_strict54_nonadj_mask c.val).testBit d.val = true := by
      simp only [Nat.testBit_and, Bool.and_eq_true]
      exact ⟨⟨hn a d (by simp) (by simp) had, hn b d (by simp) (by simp) hbd⟩, hn c d (by simp) (by simp) hcd⟩
    rw [h0, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  · simp only [hfilt, hch, hEdges]
  · unfold digraph_common_predecessor_double_edges
    rw [in522_edge_card]
    refine (congrArg Finset.card ?_).trans digraph_strict54_out_mask_double_count
    apply Finset.filter_congr
    intro x _
    have hc : ∀ y : Fin 54, (∀ z, z ∈ s(x.1, x.2) → digraph_weighted_center_strict54_graph.Adj y z) ↔
        ((digraph_strict54_out_mask y.val).testBit x.1.val = true ∧ (digraph_strict54_out_mask y.val).testBit x.2.val = true) := by
      intro y
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, hA]
    have hcard : ∀ (inst : DecidablePred fun p => ∀ z ∈ s(x.1, x.2), digraph_weighted_center_strict54_graph.Adj p z),
        (@Finset.filter _ _ inst Finset.univ).card = (Finset.univ.filter fun p : Fin 54 =>
          (digraph_strict54_out_mask p.val).testBit x.1.val = true ∧ (digraph_strict54_out_mask p.val).testBit x.2.val = true).card := by
      intro inst
      refine congrArg Finset.card ?_
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc y
    rw [hcard, hJ]
    constructor
    · rintro ⟨h1, ⟨_, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, ⟨ne_of_lt h1, h2⟩, h3⟩
