import AFTD.Prelude
import AFTD.Kb.Tcs.Op75ParseNat
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_parse_nat_complete

Topic: np_completeness   Node: fd6df7c76aad

Provenance: helper lemma. OP-75: canonical binary natural parser for the subset-sum-to-network compiler.

The parser accepts every canonical natural encoding with an arbitrary suffix and returns the value, suffix and correct nonzero flag.
-/

theorem op75_parse_nat_complete (n : ℕ) (rest : List Bool) :
    op75_parse_nat (relu_encode_nat n ++ rest) = some (n, rest, decide (n ≠ 0)) := by
  induction n using Nat.strong_induction_on generalizing rest with
  | h n ih =>
      by_cases hz : n = 0
      · subst n
        simp [relu_encode_nat, op75_parse_nat]
      · have hn : 0 < n := Nat.pos_of_ne_zero hz
        have hd : n / 2 < n := Nat.div_lt_self hn (by omega)
        have henc : relu_encode_nat n = true :: decide (n % 2 = 1) :: relu_encode_nat (n / 2) := by
          simp only [relu_encode_nat, Nat.digits_def' (by omega : 1 < 2) hn,
            List.flatMap_cons, List.cons_append, List.nil_append]
        have hflag : (decide (n / 2 ≠ 0) || decide (n % 2 = 1)) = true := by
          by_cases hq : n / 2 = 0
          · have hm : n % 2 = 1 := by
              have he := Nat.mod_add_div n 2
              have hr := Nat.mod_lt n (by omega : 0 < 2)
              omega
            simp [hq, hm]
          · simp [hq]
        have hb : (decide (n % 2 = 1)).toNat = n % 2 := by
          have hr := Nat.mod_lt n (by omega : 0 < 2)
          have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
          rcases hcases with hc | hc <;> simp [hc]
        rw [henc]
        simp only [List.cons_append, op75_parse_nat, ih (n/2) hd rest, hflag, Bool.true_eq_false,
          ↓reduceIte]
        rw [hb]
        have he := Nat.mod_add_div n 2
        simp only [decide_eq_true hz]
        rw [he]
