import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_wild_number_le_of_block_cut_condition

Topic: graphs   Node: f9ad52b94d93

Provenance: helper lemma. Helper for OP-306 and its proposed permutation-event proof; arXiv:2610.22142, Section 3.3.2, the seal-free block-partition criterion. The hypotheses are stated directly as crossing edges for every block cut; no properness or minimum-color hypothesis is needed for this implication.

Let a nonempty complete graph have a vertex-to-block map p and one root r(i) in each of q blocks. If every used color has an edge crossing every nontrivial cut of the block labels, the wild number is at most n-q. The witness joins every nonroot vertex to its block root.
-/

theorem simple_graph_wild_number_le_of_block_cut_condition
    {n q : ℕ} {α : Type*} (hn : 0 < n)
    (γ : (⊤ : SimpleGraph (Fin n)).edgeSet → α)
    (p : Fin n → Fin q) (r : Fin q → Fin n)
    (hr : ∀ i, p (r i) = i)
    (hcut : ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin q)),
      S.Nonempty → S ≠ Finset.univ →
      ∃ u v : Fin n, ∃ huv : u ≠ v,
        p u ∈ S ∧ p v ∉ S ∧
        γ ⟨s(u, v), by simpa using huv⟩ = γ e) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ ≤ n - q := by
  classical
  let roots : Finset (Fin n) := Finset.univ.image r
  let W : Finset (Sym2 (Fin n)) :=
    (Finset.univ \ roots).image (fun v => s(v, r (p v)))
  have hnonroot : ∀ v : Fin n, v ≠ r (p v) → v ∉ roots := by
    intro v hv hvroot
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvroot
    apply hv
    rw [← hi, hr]
  have hWedge : (↑W : Set (Sym2 (Fin n))) ⊆ (⊤ : SimpleGraph (Fin n)).edgeSet := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have hvr : v ≠ r (p v) := by
      intro h
      apply (Finset.mem_sdiff.mp hv).2
      exact Finset.mem_image.mpr ⟨p v, Finset.mem_univ _, h.symm⟩
    simpa using hvr
  have hWconn : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) γ ↑W := by
    refine ⟨hWedge, ?_⟩
    intro e
    let H : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet
      ({f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, γ ⟨f, hf⟩ = γ e} ∪ ↑W)
    have hstar : ∀ v : Fin n, H.Reachable v (r (p v)) := by
      intro v
      by_cases hv : v = r (p v)
      · rw [← hv]
      · apply SimpleGraph.Adj.reachable
        change (SimpleGraph.fromEdgeSet _).Adj _ _
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨Or.inr ?_, hv⟩
        exact Finset.mem_image.mpr ⟨v,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnonroot v hv⟩, rfl⟩
    change H.Connected
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨?_⟩
    intro u v
    by_contra huv
    let S : Finset (Fin q) := Finset.univ.filter (fun i => H.Reachable u (r i))
    have hu : p u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar u⟩
    have hv : p v ∉ S := by
      intro h
      exact huv ((Finset.mem_filter.mp h).2.trans (hstar v).symm)
    have hS : S ≠ Finset.univ := by
      intro h
      exact hv (h.symm ▸ Finset.mem_univ (p v))
    obtain ⟨a, b, hab, ha, hb, hc⟩ := hcut e S ⟨p u, hu⟩ hS
    have hua : H.Reachable u a := (Finset.mem_filter.mp ha).2.trans (hstar a).symm
    have habH : H.Adj a b := by
      change (SimpleGraph.fromEdgeSet _).Adj _ _
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Or.inl ⟨by simpa using hab, hc⟩, hab⟩
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hua.trans (habH.reachable.trans (hstar b))⟩)
  have hinj : Function.Injective r := by
    intro i j hij
    simpa only [hr] using congrArg p hij
  have hroots : roots.card = q := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine (simple_graph_wild_number_le_of_is_color_connecting _ γ W hWconn).trans ?_
  calc W.card ≤ (Finset.univ \ roots).card := Finset.card_image_le
    _ = n - q := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hroots]
