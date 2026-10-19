import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListEqZero
import AFTD.Kb.GameTheoryEconomics.NatMexListEqOne
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# spider_mex_one_two

Topic: combinatorial_games   Node: 62f3c64f8d83

Provenance: helper lemma. step towards spider_grundy_val_one_two

The mex of the explicit closed-form option list of S(1,2,z) (8 head values plus the long block, after substituting all closed forms) equals (z+1) % 2, for z ≥ 1.
-/

lemma spider_mex_one_two_xor_ne_zero_of_sum_odd (a b : ℕ) (h : (a + b) % 2 = 1) :
    a ^^^ b ≠ 0 := by
  intro h0
  have hx := Nat.xor_mod_two_eq (m := a) (n := b)
  rw [h0, h] at hx
  exact Nat.zero_ne_one hx

lemma spider_mex_one_two_xor_ne_one_of_sum_even (a b : ℕ) (h : (a + b) % 2 = 0) :
    a ^^^ b ≠ 1 := by
  intro h1
  have hx := Nat.xor_mod_two_eq (m := a) (n := b)
  rw [h1, h] at hx
  exact absurd hx (by decide)

/-- Mex of the substituted root option list equals (z+1)%2. -/
theorem spider_mex_one_two (z : ℕ) (hz : 1 ≤ z) :
    nat_mex_list
      ([z - 2*(1 - z%2), z - 2*(1 - z%2), 1 ^^^ (1 - z%2), 1 ^^^ (1 - z%2),
        z - 2*(1 - z%2), z - 2*(1 - z%2), (z-1) ^^^ 1, (z-1) ^^^ 1] ++
       (List.range (z-1)).flatMap (fun i =>
          [(z - (i+2)) ^^^ ((i+1) ^^^ 1), (z - (i+2)) ^^^ ((i+1) ^^^ 1)]))
      = (z+1) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one z with h | h
  · have h0 : 0 ∈ ([z - 2*(1 - z%2), z - 2*(1 - z%2), 1 ^^^ (1 - z%2), 1 ^^^ (1 - z%2),
        z - 2*(1 - z%2), z - 2*(1 - z%2), (z-1) ^^^ 1, (z-1) ^^^ 1] ++
       (List.range (z-1)).flatMap (fun i =>
          [(z - (i+2)) ^^^ ((i+1) ^^^ 1), (z - (i+2)) ^^^ ((i+1) ^^^ 1)]) : List ℕ) := by
      simp [h]
    have h1 : 1 ∉ ([z - 2*(1 - z%2), z - 2*(1 - z%2), 1 ^^^ (1 - z%2), 1 ^^^ (1 - z%2),
        z - 2*(1 - z%2), z - 2*(1 - z%2), (z-1) ^^^ 1, (z-1) ^^^ 1] ++
       (List.range (z-1)).flatMap (fun i =>
          [(z - (i+2)) ^^^ ((i+1) ^^^ 1), (z - (i+2)) ^^^ ((i+1) ^^^ 1)]) : List ℕ) := by
      simp [h]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · intro hh
        exact spider_mex_one_two_xor_ne_one_of_sum_even _ _ (by omega) hh.symm
      · intro x hx hh
        have hpar : ((x+1) ^^^ 1) % 2 = (x+2) % 2 := by rw [Nat.xor_mod_two_eq]
        exact spider_mex_one_two_xor_ne_one_of_sum_even _ _ (by omega) hh.symm
    rw [nat_mex_list_eq_one _ h0 h1]
    omega
  · have h0 : 0 ∉ ([z - 2*(1 - z%2), z - 2*(1 - z%2), 1 ^^^ (1 - z%2), 1 ^^^ (1 - z%2),
        z - 2*(1 - z%2), z - 2*(1 - z%2), (z-1) ^^^ 1, (z-1) ^^^ 1] ++
       (List.range (z-1)).flatMap (fun i =>
          [(z - (i+2)) ^^^ ((i+1) ^^^ 1), (z - (i+2)) ^^^ ((i+1) ^^^ 1)]) : List ℕ) := by
      simp [h]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · intro hh
        exact spider_mex_one_two_xor_ne_zero_of_sum_odd _ _ (by omega) hh.symm
      · intro x hx hh
        have hpar : ((x+1) ^^^ 1) % 2 = (x+2) % 2 := by rw [Nat.xor_mod_two_eq]
        exact spider_mex_one_two_xor_ne_zero_of_sum_odd _ _ (by omega) hh.symm
    rw [nat_mex_list_eq_zero _ h0]
    omega
