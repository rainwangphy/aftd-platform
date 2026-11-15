import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseNat
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_parse_nat_sound

Topic: np_completeness   Node: 98c2ab61fc80

Provenance: helper lemma. OP-75: canonical binary natural parser for the subset-sum-to-network compiler.

Every successful natural parse exactly consumes the canonical encoding of its returned value and returns the correct nonzero flag.
-/

theorem op75_parse_nat_sound (w : List Bool) (n : ℕ) (rest : List Bool) (nz : Bool)
    (h : op75_parse_nat w = some (n, rest, nz)) :
    w = relu_encode_nat n ++ rest ∧ nz = decide (n ≠ 0) := by
  induction w using List.twoStepInduction generalizing n rest nz with
  | nil => simp [op75_parse_nat] at h
  | singleton head =>
      cases head with
      | false =>
          simp [op75_parse_nat] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [relu_encode_nat]
      | true => simp [op75_parse_nat] at h
  | cons_cons head bit tail ih ih2 =>
      cases head with
      | false =>
          simp [op75_parse_nat] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [relu_encode_nat]
      | true =>
          cases hp : op75_parse_nat tail with
          | none => simp [op75_parse_nat, hp] at h
          | some value =>
              rcases value with ⟨m, r, nonzero⟩
              have htail := ih m r nonzero hp
              rcases htail with ⟨hword, hnz⟩
              cases hc : nonzero || bit with
              | false => simp [op75_parse_nat, hp, hc] at h
              | true =>
                  simp [op75_parse_nat, hp, hc] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  have hne : bit.toNat ≠ 0 ∨ m ≠ 0 := by
                    cases bit <;> cases nonzero <;> simp_all
                  have hdig : Nat.digits 2 (bit.toNat + 2*m) = bit.toNat :: Nat.digits 2 m := by
                    apply Nat.digits_add 2 (by omega) bit.toNat m
                    · cases bit <;> decide
                    · exact hne
                  have hbit : decide (bit.toNat = 1) = bit := by cases bit <;> decide
                  constructor
                  · simpa only [relu_encode_nat, hdig, List.flatMap_cons, List.cons_append,
                      List.nil_append, List.append_assoc, hbit] using congrArg (fun z => true :: bit :: z) hword
                  · have hn : bit.toNat + 2*m ≠ 0 := by omega
                    exact (decide_eq_true hn).symm
