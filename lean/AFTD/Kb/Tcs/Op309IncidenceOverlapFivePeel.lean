import AFTD.Prelude

/-!
# op309_incidence_overlap_five_peel

Topic: graphs   Node: 0fce335a9df1

Provenance: helper lemma. OP-309 port-class incidence peeling route, IN-1099.

In every nonempty subset of class vertices, some class has at most four distinct neighbors and at most five host-counted neighbor incidences.
-/

def op309_incidence_overlap_five_peel{A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (I : SimpleGraph (A ⊕ B))
    [DecidableRel I.Adj] : Prop :=
  ∀ S : Finset A, S.Nonempty → ∃ a ∈ S,
    (S.filter fun a' => a' ≠ a ∧ ∃ b : B,
      I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)).card ≤ 4 ∧
    (∑ b : B, if I.Adj (.inl a) (.inr b) then
      (S.filter fun a' => I.Adj (.inl a') (.inr b)).card - 1 else 0) ≤ 5
