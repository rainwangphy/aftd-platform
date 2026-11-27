import AFTD.Prelude
import AFTD.Kb.Tcs.Op309GraphFourDegenerate

/-!
# op309_locally_injective_fourdeg_lift

Topic: graphs   Node: 49086dedca6f

Provenance: helper lemma. Quotient-cover lifting for the maximum-forest repair construction in OP-309; experiment 43519.

A graph admitting a locally injective adjacency-preserving map to a four-degenerate graph is itself four-degenerate.
-/

theorem op309_locally_injective_fourdeg_lift
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (Q : SimpleGraph X) (H : SimpleGraph Y) (f : X → Y)
    (hom : ∀ a b, Q.Adj a b → H.Adj (f a) (f b))
    (locinj : ∀ v a b, Q.Adj v a → Q.Adj v b → f a = f b → a = b)
    (hH : op309_graph_four_degenerate H) : op309_graph_four_degenerate Q := by
  classical
  intro S hS
  obtain ⟨w,hw,T,hT,hcover⟩ := hH (S.image f) (hS.image f)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
  let N := S.filter fun u => Q.Adj v u
  have hNinj : Set.InjOn f (↑N : Set X) := by
    intro a ha b hb hab
    exact locinj v a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hNsub : N.image f ⊆ T := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    have hu' := Finset.mem_filter.mp hu
    exact hcover (f u) (Finset.mem_image.mpr ⟨u,hu'.1,rfl⟩) (hom v u hu'.2)
  refine ⟨v,hv,N,?_,?_⟩
  · calc
      N.card = (N.image f).card := (Finset.card_image_of_injOn hNinj).symm
      _ ≤ T.card := Finset.card_le_card hNsub
      _ ≤ 4 := hT
  · intro u hu hadj
    exact Finset.mem_filter.mpr ⟨hu,hadj⟩
