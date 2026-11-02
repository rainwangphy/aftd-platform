import AFTD.Prelude

/-!
# swf_is_finitely_anonymous

Topic: social_choice   Node: 53bab81521e9

Provenance: formalization of a published result. Source: arXiv:2610.38824, Definition 2

A social welfare function W on infinite utility streams in [0, 1] satisfies finite anonymity if for every stream x and every permutation π of ℕ with finite support, W(x ∘ π) = W(x).
-/

/-- A social welfare function satisfies finite anonymity if it is invariant under permutations of indices with finite support. -/
def swf_is_finitely_anonymous (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ) : Prop :=
  ∀ (x : Stream' (Set.Icc (0 : ℝ) 1)) (π : Equiv.Perm ℕ),
    {t : ℕ | π t ≠ t}.Finite → W (x ∘ π) = W x
