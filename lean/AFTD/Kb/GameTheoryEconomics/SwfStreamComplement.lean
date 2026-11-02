import AFTD.Prelude

/-!
# swf_stream_complement

Topic: social_choice   Node: 73cd101b226c

Provenance: helper lemma. step towards swf_upper_restricted_dominance_exists

The order-reversing complement of a utility stream in [0,1]^ℕ: each entry v is replaced by 1 - v.
-/

/-- Pointwise complement x ↦ (t ↦ 1 - x t) of a utility stream; it reverses the pointwise order on [0,1]^ℕ. -/
noncomputable def swf_stream_complement (x : Stream' (Set.Icc (0 : ℝ) 1)) : Stream' (Set.Icc (0 : ℝ) 1) := fun t => ⟨1 - (x t : ℝ), by
    have h1 : (0:ℝ) ≤ (x t : ℝ) := (x t).2.1
    have h2 : (x t : ℝ) ≤ 1 := (x t).2.2
    exact ⟨by linarith, by linarith⟩⟩
