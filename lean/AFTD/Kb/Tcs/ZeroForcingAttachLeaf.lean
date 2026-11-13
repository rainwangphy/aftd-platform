import AFTD.Prelude

/-!
# zero_forcing_attach_leaf

Topic: graphs   Node: fd800e5c0c7a

Provenance: helper lemma. A graph operation for relating root-exposed forts to pendant-vertex forcing, towards OP-1399; compare the related leaf inequality in arXiv:2605.10836, Section 3, Lemma 4.

The graph obtained from G by adjoining one new vertex adjacent only to the root r.
-/

def zero_forcing_attach_leaf {V : Type*} (G : SimpleGraph V) (r : V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, none => False
    | none, some v => v = r
    | some u, none => u = r
    | some u, some v => G.Adj u v
  symm := ⟨by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact h.elim
      | some v => exact h
    | some u =>
      cases y with
      | none => exact h
      | some v => exact h.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | none => simp
    | some v => exact G.irrefl⟩
