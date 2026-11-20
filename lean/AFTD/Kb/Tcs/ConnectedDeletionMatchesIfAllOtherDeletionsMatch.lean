import AFTD.Prelude
import AFTD.Kb.Tcs.Op2037SubgraphFintype
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.Supp

/-!
# connected_deletion_matches_if_all_other_deletions_match

Topic: graphs   Node: 6dc2e0253c1f

Provenance: helper lemma. Tutte vertex-deletion exchange step in the corrected OP-1957 saturated-triple route.

If deleting u from a finite graph leaves a connected graph, and deleting any vertex other than u leaves a graph with a perfect matching, then deleting u also leaves a graph with a perfect matching.
-/

open SimpleGraph

lemma in1076_odd_components_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (φ : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  apply Set.ncard_congr'
  apply φ.connectedComponentEquiv.subtypeEquiv
  intro c
  change Odd c.supp.ncard ↔ Odd (φ.connectedComponentEquiv c).supp.ncard
  rw [Set.ncard_congr' (SimpleGraph.ConnectedComponent.isoEquivSupp φ c)]

lemma in1076_connected_even_no_empty_violator {V : Type*} [Finite V] (G : SimpleGraph V)
    (hconn : G.Connected) (heven : Even (Nat.card V)) : ¬ G.IsTutteViolator ∅ := by
  letI := hconn.preconnected.subsingleton_connectedComponent
  have hle : G.oddComponents.ncard ≤ 1 := (Set.ncard_le_one).mpr (by
    intro a ha b hb
    exact Subsingleton.elim a b)
  have hnodd : ¬ Odd G.oddComponents.ncard := by
    intro h
    exact (Nat.not_odd_iff_even.mpr heven) ((G.odd_ncard_oddComponents).mp h)
  have hz : G.oddComponents.ncard = 0 := by
    by_contra hn
    have : G.oddComponents.ncard = 1 := by omega
    apply hnodd
    rw [this]
    decide
  unfold SimpleGraph.IsTutteViolator
  rw [SimpleGraph.Subgraph.deleteVerts_empty, Set.ncard_empty]
  rw [in1076_odd_components_iso _ _ (SimpleGraph.Subgraph.topIso)]
  omega

noncomputable def in1076_exchange_delete_iso {V : Type*} (G : SimpleGraph V)
    (u b : V) (S : Set V) (hb : b ∈ S) :
    ((⊤ : (G.induce {v | v ≠ u}).Subgraph).deleteVerts
        {v | v.val ∈ S}).coe ≃g
    ((⊤ : (G.induce {v | v ≠ b}).Subgraph).deleteVerts
        {v | v.val = u ∨ v.val ∈ S}).coe where
  toFun := fun ⟨⟨v, hvu⟩, hv⟩ => by
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff,
      Set.mem_univ, true_and, Set.mem_setOf_eq] at hv
    have hvb : v ≠ b := by
      intro h
      apply hv
      rw [h]
      exact hb
    refine ⟨⟨v, hvb⟩, ?_⟩
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff,
      Set.mem_univ, true_and, Set.mem_setOf_eq, not_or]
    exact ⟨hvu, hv⟩
  invFun := fun ⟨⟨v, hvb⟩, hv⟩ => by
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff,
      Set.mem_univ, true_and, Set.mem_setOf_eq, not_or] at hv
    refine ⟨⟨v, hv.1⟩, ?_⟩
    simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_diff,
      Set.mem_univ, true_and, Set.mem_setOf_eq]
    exact hv.2
  left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
  map_rel_iff' := by
    rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨c, hc⟩, hc'⟩
    have has : a ∉ S := by simpa [Subgraph.deleteVerts_verts, Subgraph.verts_top] using ha'
    have hcs : c ∉ S := by simpa [Subgraph.deleteVerts_verts, Subgraph.verts_top] using hc'
    change a ≠ u at ha
    change c ≠ u at hc
    simp [Subgraph.coe_adj, Subgraph.top_adj, ha, hc, has, hcs]

theorem connected_deletion_matches_if_all_other_deletions_match
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u : V)
    (hconn : (G.induce {v | v ≠ u}).Connected)
    (hother : ∀ b : V, b ≠ u →
      ∃ P : (G.induce {v | v ≠ b}).Subgraph, P.IsPerfectMatching) :
    ∃ P : (G.induce {v | v ≠ u}).Subgraph, P.IsPerfectMatching := by
  classical
  obtain ⟨⟨b, hbu⟩⟩ := hconn.nonempty
  obtain ⟨P, hP⟩ := hother b hbu
  have heven : Even (Nat.card {v : V // v ≠ u}) := by
    rw [Nat.card_eq_fintype_card]
    have hc : Fintype.card {v : V // v ≠ u} = Fintype.card {v : V // v ≠ b} := by
      simp [Fintype.card_subtype_compl]
    rw [hc]
    exact hP.even_card
  by_contra hnmatch
  have hno : ∀ P : (G.induce {v | v ≠ u}).Subgraph, ¬P.IsPerfectMatching := by
    simpa using hnmatch
  obtain ⟨S, hS⟩ := (G.induce {v | v ≠ u}).exists_isTutteViolator hno heven
  have hSne : S.Nonempty := by
    by_contra h
    have : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    subst S
    exact (in1076_connected_even_no_empty_violator _ hconn heven) hS
  obtain ⟨⟨v, hvu⟩, hvS⟩ := hSne
  let S0 : Set V := Subtype.val '' S
  have hv0 : v ∈ S0 := ⟨⟨v, hvu⟩, hvS, rfl⟩
  have hu0 : u ∉ S0 := by
    rintro ⟨⟨w, hwu⟩, hwS, hw⟩
    exact hwu hw
  let T : Set {w : V // w ≠ v} := {w | w.val = u ∨ w.val ∈ S0}
  have hvu' : v ≠ u := hvu
  have himage : Subtype.val '' T = insert u (S0 \ {v}) := by
    ext w
    constructor
    · rintro ⟨⟨z, hzv⟩, hzT, rfl⟩
      change z = u ∨ z ∈ S0 at hzT
      rcases hzT with hzU | hzS
      · exact Set.mem_insert_iff.mpr (Or.inl hzU)
      · change z = u ∨ z ∈ S0 ∧ z ≠ v
        exact Or.inr ⟨hzS, hzv⟩
    · intro hw
      rcases Set.mem_insert_iff.mp hw with hwU | ⟨hwS, hwv⟩
      · have hwv : w ≠ v := by intro h; exact hvu' (h.symm.trans hwU)
        exact ⟨⟨w, hwv⟩, Or.inl hwU, rfl⟩
      · have hwv' : w ≠ v := by simpa using hwv
        exact ⟨⟨w, hwv'⟩, Or.inr hwS, rfl⟩
  have hcard : T.ncard = S.ncard := by
    have h₁ : (Subtype.val '' S).ncard = S.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    have h₂ : (Subtype.val '' T).ncard = T.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    rw [← h₂, himage, Set.ncard_exchange hu0 hv0]
    exact h₁
  have hpre : {w : {v : V // v ≠ u} | w.val ∈ S0} = S := by
    ext w
    constructor
    · rintro ⟨s, hs, he⟩
      have : s = w := Subtype.ext he
      simpa [this] using hs
    · intro hw
      exact ⟨w, hw, rfl⟩
  have hiso := in1076_exchange_delete_iso G u v S0 hv0
  have hodd := in1076_odd_components_iso _ _ hiso
  have hodd' : ((⊤ : (G.induce {w | w ≠ u}).Subgraph).deleteVerts S).coe.oddComponents.ncard =
      ((⊤ : (G.induce {w | w ≠ v}).Subgraph).deleteVerts T).coe.oddComponents.ncard := by
    have heq := congrArg (fun X : Set {w : V // w ≠ u} =>
      ((⊤ : (G.induce {w | w ≠ u}).Subgraph).deleteVerts X).coe.oddComponents.ncard) hpre
    exact heq.symm.trans hodd
  have hviol : (G.induce {w | w ≠ v}).IsTutteViolator T := by
    unfold SimpleGraph.IsTutteViolator at hS ⊢
    rw [hcard, ← hodd']
    exact hS
  obtain ⟨P', hP'⟩ := hother v hvu'
  exact (not_isTutteViolator_of_isPerfectMatching hP' T) hviol
