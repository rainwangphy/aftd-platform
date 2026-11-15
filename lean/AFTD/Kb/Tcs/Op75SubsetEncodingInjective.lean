import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.ReluEncodeNat
import AFTD.Kb.Tcs.ReluNetwork3EncodeInjective

/-!
# op75_subset_encoding_injective

Topic: np_completeness   Node: 5b965179bb4d

Provenance: helper lemma. OP-75 one-pass subset-sum construction, arXiv:2610.06092; binary source encoding for a machine-level reduction.

The binary source encoding uniquely determines the finite list of weights and the target.
-/

lemma op75_encode_parts_injective890 (as bs : List ℕ) (t u : ℕ)
    (h : op75_subset_encoding as t = op75_subset_encoding bs u) : as = bs ∧ t = u := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil =>
          simp only [op75_subset_encoding, List.flatMap_nil, List.nil_append, List.cons_append,
            List.nil_append, List.cons.injEq, true_and] at h
          exact ⟨rfl, (relu_encode_nat_prefix t u [] [] (by simpa using h)).1⟩
      | cons b bs => simp [op75_subset_encoding] at h
  | cons a as ih =>
      cases bs with
      | nil => simp [op75_subset_encoding] at h
      | cons b bs =>
          have hp : relu_encode_nat a ++ op75_subset_encoding as t =
                    relu_encode_nat b ++ op75_subset_encoding bs u := by
            simpa only [op75_subset_encoding, List.flatMap_cons, List.cons_append,
              List.append_assoc, List.cons.injEq, true_and] using h
          obtain ⟨hab, hs⟩ := relu_encode_nat_prefix a b _ _ hp
          obtain ⟨has, htu⟩ := ih bs hs
          exact ⟨by simp [hab, has], htu⟩

theorem op75_subset_encoding_injective : Function.Injective (fun v : List ℕ × ℕ => op75_subset_encoding v.1 v.2) := by
  rintro ⟨as,t⟩ ⟨bs,u⟩ h
  obtain ⟨rfl,rfl⟩ := op75_encode_parts_injective890 as bs t u h
  rfl
