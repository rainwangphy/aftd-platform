import AFTD.Prelude

/-!
# is_anonymous_rule

Topic: social_choice   Node: cc646d8a4739

Provenance: formalization of a published result. Source: arXiv:2611.26224 Sec. 6, p. 13

A voting rule f : (N → LinearOrder A) → A mapping profiles of linear orders on A to alternatives is anonymous if for every profile P and permutation σ of voters N, f (fun i => P (σ i)) = f P.
-/

/-- A voting rule is anonymous if permuting voters does not change the outcome. -/
def is_anonymous_rule {N A : Type*} (f : (N → LinearOrder A) → A) : Prop :=
  ∀ (P : N → LinearOrder A) (σ : Equiv.Perm N), f (fun i => P (σ i)) = f P
