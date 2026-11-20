import AFTD.Prelude

/-!
# shared_shore_global_endpoint_degree_budget

Topic: graphs   Node: f92240e2d3bf

Provenance: helper lemma. Global shared-shore degree budget for the OP-1957 crossing-cut campaign.

For a family of pairwise disjoint endpoint sets P(a), all disjoint from W, suppose every vertex q of Q(i) is adjacent to W and, whenever q also belongs to Q(a), to every vertex of P(a). If each q in Q(i) has degree at most d, the sum over a of |Q(i) ∩ Q(a)| times |P(a)| plus |Q(i)| times |W| is at most |Q(i)|d.
-/

theorem shared_shore_global_endpoint_degree_budget
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ)
    (F : Finset I) (Q P : I → Finset V) (W : Finset V) (i : I)
    (hi : i ∈ F)
    (hdisj : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → Disjoint (P a) (P b))
    (hW : ∀ a ∈ F, Disjoint W (P a))
    (hWneighbors : ∀ q ∈ Q i, ∀ w ∈ W, H.Adj q w)
    (hPneighbors : ∀ a ∈ F, ∀ q ∈ Q i ∩ Q a, ∀ z ∈ P a, H.Adj q z)
    (hdegree : ∀ q ∈ Q i, (H.neighborFinset q).card ≤ d) :
    (∑ a ∈ F, (Q i ∩ Q a).card * (P a).card) + (Q i).card * W.card ≤ (Q i).card * d := by
  classical
  have hlocal : ∀ q ∈ Q i, W.card + (∑ a ∈ F, if q ∈ Q a then (P a).card else 0) ≤ d := by
    intro q hq
    let Fq := F.filter (fun a => q ∈ Q a)
    have hpair : (Fq : Set I).PairwiseDisjoint P := by
      intro a ha b hb hab
      apply hdisj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    have hWdisj : Disjoint W (Fq.biUnion P) := by
      apply (Finset.disjoint_biUnion_right W Fq P).mpr
      intro a ha
      exact hW a (Finset.mem_filter.mp ha).1
    have hsub : W ∪ Fq.biUnion P ⊆ H.neighborFinset q := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_union.mp hx with hxW | hxP
      · exact hWneighbors q hq x hxW
      · obtain ⟨a, ha, hxPa⟩ := Finset.mem_biUnion.mp hxP
        have haF := (Finset.mem_filter.mp ha).1
        have hqa := (Finset.mem_filter.mp ha).2
        exact hPneighbors a haF q (Finset.mem_inter.mpr ⟨hq,hqa⟩) x hxPa
    have h := (Finset.card_le_card hsub).trans (hdegree q hq)
    rw [Finset.card_union_of_disjoint hWdisj, Finset.card_biUnion hpair] at h
    simpa only [Fq, Finset.sum_filter] using h
  have hsum : (∑ q ∈ Q i, ∑ a ∈ F, if q ∈ Q a then (P a).card else 0) =
      ∑ a ∈ F, (Q i ∩ Q a).card * (P a).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_filter]
    have heq : (Q i).filter (fun q => q ∈ Q a) = Q i ∩ Q a := by
      ext q
      simp
    rw [heq]
    simp
  have htotal := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, hsum] at htotal
  have hleft : (∑ q ∈ Q i, W.card) = (Q i).card * W.card := by simp
  have hright : (∑ q ∈ Q i, d) = (Q i).card * d := by simp
  rw [hleft, hright] at htotal
  simpa only [Nat.add_comm] using htotal
