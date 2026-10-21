import AFTD.Prelude
import AFTD.Kb.Tcs.Op258HasMonoClique

/-!
# op_258_mono_clique_of_fiber_gt_turan

Topic: combinatorics   Node: 291e8d7661b2

Provenance: helper lemma. step towards op_258_forces_step

If a single colour class of an edge colouring of K_n has strictly more edges than the Turán bound for K_{r+1}-free graphs (r ≥ 1), then the colouring has a monochromatic K_{r+1} in that colour.
-/

/-- A colour class larger than the Turán bound forces a monochromatic clique in that colour. -/
theorem op_258_mono_clique_of_fiber_gt_turan (n r : ℕ) (hr : 1 ≤ r)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (i : ℕ+)
    (h : (Finset.univ.filter (fun e => c e = i)).card >
        (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2) :
    op_258_has_mono_clique n c (r + 1) := by
  classical
  set F : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet := Finset.univ.filter (fun e => c e = i) with hF
  set S : Finset (Sym2 (Fin n)) := F.image (fun e : (SimpleGraph.completeGraph (Fin n)).edgeSet => (e : Sym2 (Fin n))) with hS
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin n), G = SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n))) :=
    ⟨_, rfl⟩
  have hsub : (S : Set (Sym2 (Fin n))) ⊆ Sym2.diagSetᶜ := by
    have aux : ∀ z : Sym2 (Fin n), z ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet → ¬ z.IsDiag := by
      intro z hz
      induction z using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at hz
        rw [SimpleGraph.top_adj] at hz
        rw [Sym2.mk_isDiag_iff]
        exact hz
    intro x hx
    rw [hS, Finset.coe_image] at hx
    obtain ⟨e, _, rfl⟩ := hx
    rw [Set.mem_compl_iff, Sym2.mem_diagSet]
    exact aux _ e.2
  have hGedge : G.edgeSet = (S : Set (Sym2 (Fin n))) := by
    rw [hG, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨h1, _⟩; exact h1
    · intro h1
      exact ⟨h1, by have := hsub h1; simpa using this⟩
  by_contra hn
  have hGcf : G.CliqueFree (r + 1) := by
    intro t ht
    apply hn
    refine ⟨t, i, ht.card_eq, ?_⟩
    intro u v hu hv huv
    have hpw : (↑t : Set (Fin n)).Pairwise G.Adj := (SimpleGraph.isClique_iff G).mp ht.isClique
    have hadj : G.Adj u v := hpw hu hv huv
    have hmem : Sym2.mk u v ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hadj
    rw [hGedge] at hmem
    rw [hS, Finset.mem_coe, Finset.mem_image] at hmem
    obtain ⟨e, heF, hev⟩ := hmem
    have heF' : c e = i := by
      rw [hF, Finset.mem_filter] at heF
      exact heF.2
    have key : ∀ (hh : Sym2.mk u v ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet), c ⟨Sym2.mk u v, hh⟩ = i := by
      intro hh
      have hx : (⟨Sym2.mk u v, hh⟩ : (SimpleGraph.completeGraph (Fin n)).edgeSet) = e := Subtype.ext hev.symm
      rw [hx]; exact heF'
    exact key _
  have hbound := SimpleGraph.CliqueFree.card_edgeFinset_le (V := Fin n) (G := G) (r := r) hGcf
  simp only [Fintype.card_fin] at hbound
  rw [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] at hbound
  have hNat : Nat.card ↥G.edgeSet = F.card := by
    rw [Nat.card_congr (Equiv.setCongr hGedge), Nat.card_coe_set_eq, Set.ncard_coe_finset, hS]
    exact Finset.card_image_of_injective _ (fun a b hab => Subtype.ext hab)
  rw [hNat] at hbound
  omega
