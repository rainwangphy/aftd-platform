import AFTD.Prelude
import AFTD.Kb.Tcs.ExistsSignedNonzeroLinearForms

/-!
# simple_graph_bipartite_additive_lists_of_edge_assignment

Topic: graphs   Node: 822530b3066f

Provenance: helper lemma. Helper for OP-494 in arXiv:2610.30174, following the additive-list coloring argument of arXiv:2302.02190v3, Corollary 5.3. Take the union of the two neighbor sets for each edge, negate the lists on one bipartition class, and recover distinct natural neighborhood sums from the nonzero signed evaluations.

A finite bipartite graph admits an additive coloring from arbitrary finite natural label lists when each list size exceeds the number of edges assigned to that endpoint.
-/

open scoped BigOperators

theorem simple_graph_bipartite_additive_lists_of_edge_assignment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hbip : G.IsBipartite)
    (tail : G.edgeSet → V) (htail : ∀ e : G.edgeSet, tail e ∈ (e : Sym2 V))
    (L : V → Finset ℕ)
    (hL : ∀ v, (Finset.univ.filter (fun e => tail e = v)).card < (L v).card) :
    ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧
      ∀ ⦃u v : V⦄, G.Adj u v →
        ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w := by
  classical
  obtain ⟨c⟩ := hbip
  let A : G.edgeSet → Finset V := fun e =>
    (e : Sym2 V).toFinset.biUnion (fun v => G.neighborFinset v)
  have htailA : ∀ e, tail e ∈ A e := by
    rintro ⟨⟨u, v⟩, huv⟩
    have h := htail ⟨s(u, v), huv⟩
    simp only [Sym2.mem_iff] at h
    change tail ⟨s(u, v), huv⟩ ∈
      (s(u, v).toFinset.biUnion (fun v => G.neighborFinset v))
    rcases h with h | h
    · apply Finset.mem_biUnion.mpr
      refine ⟨v, by simp, ?_⟩
      rw [h, G.mem_neighborFinset]
      exact (G.mem_edgeSet.mp huv).symm
    · apply Finset.mem_biUnion.mpr
      refine ⟨u, by simp, ?_⟩
      rw [h, G.mem_neighborFinset]
      exact G.mem_edgeSet.mp huv
  let L' : V → Finset ℤ := fun v =>
    (L v).image (fun a : ℕ => if c v = 0 then -(a : ℤ) else (a : ℤ))
  have hL' : ∀ v, (Finset.univ.filter (fun e => tail e = v)).card < (L' v).card := by
    intro v
    have hinj : Function.Injective (fun a : ℕ => if c v = 0 then -(a : ℤ) else (a : ℤ)) := by
      intro a b hab
      by_cases hc : c v = 0
      · simp only [if_pos hc, neg_inj] at hab
        exact Int.ofNat_inj.mp hab
      · simp only [if_neg hc] at hab
        exact Int.ofNat_inj.mp hab
    simpa only [L', Finset.card_image_of_injective _ hinj] using hL v
  obtain ⟨x, hx, hxne⟩ := exists_signed_nonzero_linear_forms A tail htailA L' hL'
  have hx' : ∀ v, ∃ a ∈ L v, x v = if c v = 0 then -(a : ℤ) else (a : ℤ) := by
    intro v
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp (hx v)
    exact ⟨a, ha, hax.symm⟩
  choose f hf hxf using hx'
  have hcolors {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : c v = c w := by
    have hv := c.valid huv
    have hw := c.valid huw
    apply Fin.ext
    have hu' := (c u).isLt
    have hv' := (c v).isLt
    have hw' := (c w).isLt
    omega
  have hsum {u v : V} (huv : G.Adj u v) :
      (∑ w ∈ G.neighborFinset u, x w) =
        if c v = 0 then -(∑ w ∈ G.neighborFinset u, (f w : ℤ))
        else ∑ w ∈ G.neighborFinset u, (f w : ℤ) := by
    split_ifs with hv0
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hxf, ← hcolors huv ((G.mem_neighborFinset u w).mp hw)]
      simp [hv0]
    · apply Finset.sum_congr rfl
      intro w hw
      rw [hxf, ← hcolors huv ((G.mem_neighborFinset u w).mp hw)]
      simp [hv0]
  refine ⟨f, hf, ?_⟩
  intro u v huv heq
  have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro w hwu hwv
    have heq := hcolors ((G.mem_neighborFinset u w).mp hwu).symm
      ((G.mem_neighborFinset v w).mp hwv).symm
    exact c.valid huv heq
  have hne := hxne ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  change (∑ w ∈ s(u, v).toFinset.biUnion (fun v => G.neighborFinset v), x w) ≠ 0 at hne
  simp only [Sym2.toFinset_mk_eq, Finset.biUnion_insert, Finset.singleton_biUnion] at hne
  rw [Finset.sum_union hdisj, hsum huv, hsum huv.symm] at hne
  have hs : (∑ w ∈ G.neighborFinset u, (f w : ℤ)) =
      ∑ w ∈ G.neighborFinset v, (f w : ℤ) := by
    exact_mod_cast heq
  by_cases hu0 : c u = 0
  · have hv0 : c v ≠ 0 := fun hv0 => c.valid huv (hu0.trans hv0.symm)
    simp [hu0, hv0, hs] at hne
  · have hv0 : c v = 0 := by
      have hneq := c.valid huv
      apply Fin.ext
      have hu' := (c u).isLt
      have hv' := (c v).isLt
      omega
    simp [hu0, hv0, hs] at hne
