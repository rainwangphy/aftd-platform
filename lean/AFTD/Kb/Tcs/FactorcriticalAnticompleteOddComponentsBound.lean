import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_anticomplete_odd_components_bound

Topic: graphs   Node: 128a9b6bbdf0

Provenance: helper lemma. OP-1957; factor-critical component obstruction in the all-k saturated-block boundary route.

In a finite 1-factor-critical graph, if U is anticomplete to L minus U and L contains a vertex outside U, then the number of odd components induced by U is at most the number of vertices outside L.
-/

theorem factorcritical_anticomplete_odd_components_bound
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcrit : is_k_factor_critical H 1) (U L : Finset V) (hUL : U ⊆ L)
    (z : V) (hzL : z ∈ L) (hzU : z ∉ U)
    (hanti : ∀ u ∈ U, ∀ v ∈ L, v ∉ U → ¬ H.Adj u v) :
    (H.induce {v | v ∈ U}).oddComponents.ncard ≤ ((Finset.univ : Finset V) \ L).card := by
  classical
  obtain ⟨M, hM⟩ := hcrit {z} (Finset.card_singleton z)
  have hmemW : ∀ x : V, x ∈ ((({z} : Finset V) : Set V))ᶜ ↔ x ≠ z := by intro x; simp
  set GU := H.induce {v | v ∈ U} with hGU
  let ι : ↥{v | v ∈ U} → ↥((({z} : Finset V) : Set V))ᶜ := fun a => ⟨a.1, (hmemW a.1).mpr (fun h => hzU (h ▸ a.2))⟩
  have hι : Function.Injective ι := by
    intro a b h
    have h1 : (ι a).1 = (ι b).1 := by rw [h]
    exact Subtype.ext h1
  have hkey : ∀ c ∈ GU.oddComponents, ∃ b : ↥((({z} : Finset V) : Set V))ᶜ, b.1 ∉ L ∧ ∃ a ∈ c.supp, M.Adj (ι a) b := by
    intro c hc
    by_contra hno
    push Not at hno
    let C : Set ↥((({z} : Finset V) : Set V))ᶜ := ι '' c.supp
    have hmatch : (M.induce C).IsMatching := by
      intro x hx
      obtain ⟨a', ha', rfl⟩ := hx
      obtain ⟨b, hab, huniq⟩ := hM.1 (hM.2 (ι a'))
      have hHab : H.Adj a'.1 b.1 := by
        have := M.adj_sub hab
        simpa using this
      have hbL : b.1 ∈ L := by
        by_contra hbL
        exact hno b hbL a' ha' hab
      have hbU : b.1 ∈ U := by
        by_contra hbU
        exact hanti a'.1 a'.2 b.1 hbL hbU hHab
      let b' : ↥{v | v ∈ U} := ⟨b.1, hbU⟩
      have hGUadj : GU.Adj a' b' := by simpa [GU] using hHab
      have hbc : b' ∈ c.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha' ⊢
        rw [← ha']
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hGUadj).symm
      have hbι : ι b' = b := Subtype.ext rfl
      refine ⟨b, ⟨⟨a', ha', rfl⟩, ⟨b', hbc, hbι⟩, hab⟩, fun y hy => huniq y hy.2.2⟩
    have hfin : Fintype (M.induce C).verts := Fintype.ofFinite _
    have he := hmatch.even_card
    rw [← Set.ncard_eq_toFinset_card'] at he
    have hC : (M.induce C).verts.ncard = c.supp.ncard := by
      show C.ncard = _
      exact Set.ncard_image_of_injective _ hι
    rw [hC] at he
    exact (Nat.not_even_iff_odd.mpr hc) he
  let f : GU.ConnectedComponent → V := fun c =>
    if h : c ∈ GU.oddComponents then ((hkey c h).choose).1 else z
  have hf : ∀ c ∈ GU.oddComponents, f c ∈ (((Finset.univ : Finset V) \ L : Finset V) : Set V) := by
    intro c hc
    simp only [f, dif_pos hc, Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
      true_and, Finset.mem_coe]
    exact (hkey c hc).choose_spec.1
  have hinj : Set.InjOn f GU.oddComponents := by
    intro c1 hc1 c2 hc2 heq
    obtain ⟨-, a1, ha1, hm1⟩ := (hkey c1 hc1).choose_spec
    obtain ⟨-, a2, ha2, hm2⟩ := (hkey c2 hc2).choose_spec
    have e : (hkey c1 hc1).choose = (hkey c2 hc2).choose := by
      apply Subtype.ext
      have := heq
      simp only [f, dif_pos hc1, dif_pos hc2] at this
      exact this
    rw [e] at hm1
    have hw : (hkey c2 hc2).choose ∈ M.verts := M.edge_vert hm1.symm
    have h12 : ι a1 = ι a2 := (hM.1 hw).unique hm1.symm hm2.symm
    have : a1 = a2 := hι h12
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha1 ha2
    rw [← ha1, ← ha2, this]
  have := Set.ncard_le_ncard_of_injOn f hf hinj
  rwa [Set.ncard_coe_finset] at this
