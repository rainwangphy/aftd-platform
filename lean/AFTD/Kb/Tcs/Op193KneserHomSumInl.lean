import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.GStableKneserAdj

/-!
# op_193_kneser_hom_sum_inl

Topic: graphs   Node: ccf3d1e63948

Provenance: helper lemma. Mathlib.Combinatorics.SimpleGraph.Sum

For any simple graphs G and H and any natural number k, there exists a graph homomorphism from the G-stable Kneser graph KG(G, k) to the (G ⊔ H)-stable Kneser graph KG(G ⊔ H, k).
-/

/-- Canonical embedding homomorphism from KG(G, k) into KG(G ⊔ H, k). -/
theorem op_193_kneser_hom_sum_inl {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) :
    Nonempty (GStableKneser G k →g GStableKneser (G.sum H) k) := by
  let f : { s : Finset V // G.IsNIndepSet k s } → { t : Finset (V ⊕ W) // (G.sum H).IsNIndepSet k t } :=
    fun s => ⟨s.1.map Function.Embedding.inl, by
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_map]
        rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
        dsimp [SimpleGraph.sum]
        intro h
        have : u ≠ v := by
          rintro rfl
          exact hne rfl
        exact s.2.isIndepSet hu hv this h
      · rw [Finset.card_map]
        exact s.2.card_eq⟩
  refine ⟨⟨f, ?_⟩⟩
  intro s t h
  rw [g_stable_kneser_adj] at h ⊢
  rcases h with ⟨hdisj, hne⟩
  refine ⟨(Finset.disjoint_map Function.Embedding.inl).mpr hdisj, ?_⟩
  intro h_eq
  apply hne
  ext1
  have h1 : (f s).1 = (f t).1 := by rw [h_eq]
  exact Finset.map_injective Function.Embedding.inl h1
