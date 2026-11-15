import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseSubsetAux
import AFTD.Kb.Tcs.Op75ParseNatSound
import AFTD.Kb.Tcs.Op75SubsetEncodingCons
import AFTD.Kb.Tcs.ReluEncodeNat
import AFTD.Kb.Tcs.Op75ParseNat
import AFTD.Kb.Tcs.Op75SubsetEncoding

/-!
# op75_parse_subset_aux_sound

Topic: np_completeness   Node: 9d8f20595a5c

Provenance: helper lemma. OP-75: canonical subset-sum input decoder for the width-three ReLU compiler.

Every successful fuel-bounded parse reconstructs exactly the original canonical subset-sum word.
-/

theorem op75_parse_subset_aux_sound (fuel : ℕ) (w : List Bool) (as : List ℕ) (t : ℕ)
    (h : op75_parse_subset_aux fuel w = some (as, t)) : op75_subset_encoding as t = w := by
  induction fuel generalizing w as t with
  | zero => simp [op75_parse_subset_aux] at h
  | succ fuel ih =>
      cases w with
      | nil => simp [op75_parse_subset_aux] at h
      | cons mark tail =>
          cases mark with
          | false =>
              cases hp : op75_parse_nat tail with
              | none => simp [op75_parse_subset_aux, hp] at h
              | some value =>
                  rcases value with ⟨n, rest, nz⟩
                  cases rest with
                  | nil =>
                      simp [op75_parse_subset_aux, hp] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hs := (op75_parse_nat_sound tail n [] nz hp).1
                      simpa [op75_subset_encoding] using congrArg (List.cons false) hs.symm
                  | cons b rest => simp [op75_parse_subset_aux, hp] at h
          | true =>
              cases hp : op75_parse_nat tail with
              | none => simp [op75_parse_subset_aux, hp] at h
              | some value =>
                  rcases value with ⟨a, rest, nz⟩
                  cases hq : op75_parse_subset_aux fuel rest with
                  | none => simp [op75_parse_subset_aux, hp, hq] at h
                  | some value =>
                      rcases value with ⟨bs, u⟩
                      simp [op75_parse_subset_aux, hp, hq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hs := (op75_parse_nat_sound tail a rest nz hp).1
                      have hr := ih rest bs u hq
                      rw [op75_subset_encoding_cons, hr, ← hs]
