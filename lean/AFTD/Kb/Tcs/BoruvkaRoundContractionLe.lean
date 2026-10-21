import AFTD.Prelude
import AFTD.Kb.Tcs.BoruvkaRound
import AFTD.Kb.Tcs.IsGloballyBestOutside

/-!
# boruvka_round_contraction_le

Topic: algorithms   Node: 8061311b30a8

Provenance: helper lemma. arXiv:2610.23032 Lemma 6.1

In any Borůvka round from F to F' under profile π : V → LinearOrder V on finite type V, the number of connected components Fintype.card F'.ConnectedComponent is at most Fintype.card F.ConnectedComponent / 2.
-/

/-- A Borůvka round reduces the number of connected components by at least a factor of 2 (Lemma 6.1). -/
theorem boruvka_round_contraction_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → LinearOrder V)
    (F F' : SimpleGraph V) (h_round : boruvka_round π F F') :
    Fintype.card F'.ConnectedComponent ≤ Fintype.card F.ConnectedComponent / 2 := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  classical
  rcases h_round with ⟨hF_acyc, h_le, hF'_acyc, r, g, hr, hg, hadj, heq⟩
  let f : F.ConnectedComponent → F'.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE h_le)
  have h_fibers : ∀ b ∈ (Finset.univ : Finset F'.ConnectedComponent),
      2 ≤ (Finset.filter (fun a => f a = b) (Finset.univ : Finset F.ConnectedComponent)).card := by
    intro b hb
    induction b using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      let c1 := F.connectedComponentMk v
      let c2 := F.connectedComponentMk (g c1)
      have hc1_map : f c1 = F'.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.map_mk (SimpleGraph.Hom.ofLE h_le) v
      have hr_c1 : F.connectedComponentMk (r c1) = c1 := hr c1
      have hc1_ne_c2 : c1 ≠ c2 := by
        intro he
        have hdiff := (hg c1).1
        rw [hr_c1] at hdiff
        exact hdiff he.symm
      have hc2_map : f c2 = F'.connectedComponentMk v := by
        have h1 : f c2 = F'.connectedComponentMk (g c1) :=
          SimpleGraph.ConnectedComponent.map_mk (SimpleGraph.Hom.ofLE h_le) (g c1)
        have h2 : F'.connectedComponentMk (g c1) = F'.connectedComponentMk (r c1) :=
          (heq c1).symm
        have h3 : F'.connectedComponentMk (r c1) = f (F.connectedComponentMk (r c1)) :=
          (SimpleGraph.ConnectedComponent.map_mk (SimpleGraph.Hom.ofLE h_le) (r c1)).symm
        have h4 : f (F.connectedComponentMk (r c1)) = f c1 := by rw [hr_c1]
        exact h1.trans (h2.trans (h3.trans (h4.trans hc1_map)))
      have h1 : c1 ∈ Finset.filter (fun a => f a = F'.connectedComponentMk v) Finset.univ := by
        simp [hc1_map]
      have h2 : c2 ∈ Finset.filter (fun a => f a = F'.connectedComponentMk v) Finset.univ := by
        simp [hc2_map]
      have hsub : {c1, c2} ⊆ Finset.filter (fun a => f a = F'.connectedComponentMk v) Finset.univ := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard_pair : ({c1, c2} : Finset F.ConnectedComponent).card = 2 :=
        Finset.card_pair hc1_ne_c2
      rw [← hcard_pair]
      exact Finset.card_le_card hsub
  have h_mul := Finset.mul_card_image_le_card_of_maps_to
    (f := f) (s := (Finset.univ : Finset F.ConnectedComponent)) (t := (Finset.univ : Finset F'.ConnectedComponent))
    (fun a _ => Finset.mem_univ (f a)) 2 h_fibers
  rw [Finset.card_univ, Finset.card_univ] at h_mul
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h_mul
  omega
