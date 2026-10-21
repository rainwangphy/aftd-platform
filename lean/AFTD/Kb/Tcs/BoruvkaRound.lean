import AFTD.Prelude
import AFTD.Kb.Tcs.IsGloballyBestOutside

/-!
# boruvka_round

Topic: algorithms   Node: 5160174230df

Provenance: formalization of a published result. Source: arXiv:2610.23032 Algorithm 1

A Borůvka round transitions forest F to acyclic graph F' containing F under ordinal profile π : V → LinearOrder V if there exist for each connected component c of F a representative r(c) with component c and its globally best outside vertex g(c), every added edge of F' is of the form {r(c), g(c)}, and each pair r(c), g(c) belongs to the same connected component of F'.
-/

/-- One round of Borůvka-style contraction: each component proposes its globally best outside edge and a maximal acyclic subset is added. -/
def boruvka_round {V : Type*} (π : V → LinearOrder V) (F F' : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ F ≤ F' ∧ F'.IsAcyclic ∧
  ∃ (r : F.ConnectedComponent → V) (g : F.ConnectedComponent → V),
    (∀ c, F.connectedComponentMk (r c) = c) ∧
    (∀ c, is_globally_best_outside F π (r c) (g c)) ∧
    (∀ u v, F'.Adj u v → F.Adj u v ∨ (∃ c, (u = r c ∧ v = g c) ∨ (u = g c ∧ v = r c))) ∧
    (∀ c, F'.connectedComponentMk (r c) = F'.connectedComponentMk (g c))
