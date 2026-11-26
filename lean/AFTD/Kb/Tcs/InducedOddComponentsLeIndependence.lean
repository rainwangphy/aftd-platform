import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# induced_odd_components_le_independence

Topic: graphs   Node: b2a2f565799c

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

The number of odd components of an induced finite graph is at most the independence bound of the ambient graph.
-/

theorem induced_odd_components_le_independence
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V)
    (a : ℕ) (hind : ∀ U : Finset V,
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ a) :
    (G.induce R).oddComponents.ncard ≤ a := by
  set_option maxHeartbeats 4000000 in
    classical
    let H := G.induce R
    let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let pick : O → R := fun c => c.val.nonempty_supp.choose
    have hpick : ∀ c : O, pick c ∈ c.val.supp := fun c => c.val.nonempty_supp.choose_spec
    have hinj : Function.Injective (fun c : O => (pick c).val) := by
      intro c d he
      have hv : pick c = pick d := Subtype.ext he
      apply Subtype.ext
      have hc := (SimpleGraph.ConnectedComponent.mem_supp_iff c.val (pick c)).mp (hpick c)
      have hd := (SimpleGraph.ConnectedComponent.mem_supp_iff d.val (pick d)).mp (hpick d)
      rw [hv] at hc
      exact hc.symm.trans hd
    let U : Finset V := Finset.univ.image (fun c : O => (pick c).val)
    have hUcard : U.card = H.oddComponents.ncard := by
      dsimp [U]
      rw [Finset.card_image_of_injective _ hinj]
      change O.attach.card = H.oddComponents.ncard
      rw [Finset.card_attach]
      exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
    have hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v := by
      intro u hu v hv hne hadj
      obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hv
      have hH : H.Adj (pick c) (pick d) := hadj
      have hcomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hH
      have hc := (SimpleGraph.ConnectedComponent.mem_supp_iff c.val (pick c)).mp (hpick c)
      have hd := (SimpleGraph.ConnectedComponent.mem_supp_iff d.val (pick d)).mp (hpick d)
      rw [hc,hd] at hcomp
      have hcd : c=d := Subtype.ext hcomp
      exact hne (congrArg (fun x : O => (pick x).val) hcd)
    have h := hind U hUind
    change H.oddComponents.ncard ≤ a
    omega
