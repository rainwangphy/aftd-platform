import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseAlphaBinaryPrefixCons
import AFTD.Kb.Tcs.AlphaLexicalLtConsSame
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.AlphaLexicalExampleEleven
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds

/-!
# alpha_lexical_lt_iff_inverse_prefix

Topic: combinatorics   Node: 5429ce2b1720

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

On equal-length positive encodings, lexical order is exactly inverse Gray-rank order.
-/

theorem alpha_lexical_lt_iff_inverse_prefix_low (xs : List ℕ) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 < v) :
    2 ^ (xs.sum - 1) ≤ brgc_inverse xs.sum (alpha_binary_prefix xs) := by
  match xs, hne with
  | z :: zs, _ =>
    have hz : 0 < z := hxs z (by simp)
    have hzs : ∀ v ∈ zs, 0 < v := fun v hv => hxs v (by simp [hv])
    rw [brgc_inverse_alpha_binary_prefix_cons z zs hz hzs, List.sum_cons]
    have h1 : 2 ^ (z - 1) ≤ 2 ^ z - 1 := by
      have : 2 ^ z = 2 * 2 ^ (z - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := Nat.one_le_two_pow (n := z - 1)
      omega
    calc 2 ^ (z + zs.sum - 1) = 2 ^ zs.sum * 2 ^ (z - 1) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ zs.sum * (2 ^ z - 1) := Nat.mul_le_mul_left _ h1
      _ ≤ _ := Nat.le_add_right _ _

theorem alpha_lexical_lt_iff_inverse_prefix_aux (n : ℕ) : ∀ (a b : List ℕ), a.length + b.length ≤ n → (∀ v ∈ a, 0 < v) → (∀ v ∈ b, 0 < v) → a.sum = b.sum → (alpha_lexical_lt a b ↔ brgc_inverse a.sum (alpha_binary_prefix a) < brgc_inverse b.sum (alpha_binary_prefix b)) := by
  induction n with
  | zero =>
    intro a b hl ha hb hs
    have ha0 : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb0 : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha0 hb0
    constructor
    · rintro ⟨i, hi, -⟩; simp at hi
    · intro h; exact absurd h (lt_irrefl _)
  | succ n ih =>
  intro a b hl ha hs' hs
  have hb := hs'
  cases a with
  | nil =>
    cases b with
    | nil =>
      constructor
      · rintro ⟨i, hi, -⟩; simp at hi
      · intro h; exact absurd h (lt_irrefl _)
    | cons y ys =>
      have := hb y (by simp)
      simp only [List.sum_nil, List.sum_cons] at hs; omega
  | cons x xs =>
    cases b with
    | nil =>
      have := ha x (by simp)
      simp only [List.sum_nil, List.sum_cons] at hs; omega
    | cons y ys =>
      have hx : 0 < x := ha x (by simp)
      have hy : 0 < y := hb y (by simp)
      have hxs : ∀ v ∈ xs, 0 < v := fun v hv => ha v (by simp [hv])
      have hys : ∀ v ∈ ys, 0 < v := fun v hv => hb v (by simp [hv])
      have hs' : x + xs.sum = y + ys.sum := by simpa using hs
      rw [brgc_inverse_alpha_binary_prefix_cons x xs hx hxs,
        brgc_inverse_alpha_binary_prefix_cons y ys hy hys]
      have hNx : brgc_inverse xs.sum (alpha_binary_prefix xs) < 2 ^ xs.sum :=
        brgc_inverse_lt_two_pow (alpha_binary_prefix_bounds_lt xs hxs)
      have hNy : brgc_inverse ys.sum (alpha_binary_prefix ys) < 2 ^ ys.sum :=
        brgc_inverse_lt_two_pow (alpha_binary_prefix_bounds_lt ys hys)
      by_cases hxy : x = y
      · subst hxy
        have hS : ys.sum = xs.sum := by omega
        have hl' : ys.length + xs.length ≤ n := by simp at hl; omega
        rw [alpha_lexical_lt_cons_same, ih ys xs hl' hys hxs hS]
        rw [hS] at hNy ⊢
        constructor <;> intro h <;> omega
      · -- the first cells differ
        have hlt_iff : alpha_lexical_lt (x :: xs) (y :: ys) ↔ x < y := by
          constructor
          · rintro ⟨i, hi, heq, hlt⟩
            cases i with
            | zero => simpa [alpha_signed_cell] using hlt
            | succ j =>
              have := heq 0 (by omega)
              simp [alpha_signed_cell] at this
              exact absurd this hxy
          · intro h
            refine ⟨0, by simp, fun k hk => absurd hk (by omega), ?_⟩
            simp [alpha_signed_cell]; exact_mod_cast h
        rw [hlt_iff]
        have key : ∀ (x y : ℕ) (xs ys : List ℕ), 0 < x → (∀ v ∈ xs, 0 < v) →
            x + xs.sum = y + ys.sum → x < y →
            brgc_inverse xs.sum (alpha_binary_prefix xs) < 2 ^ xs.sum →
            brgc_inverse ys.sum (alpha_binary_prefix ys) < 2 ^ ys.sum →
            2 ^ xs.sum * (2 ^ x - 1) + (2 ^ xs.sum - 1 - brgc_inverse xs.sum (alpha_binary_prefix xs)) <
            2 ^ ys.sum * (2 ^ y - 1) + (2 ^ ys.sum - 1 - brgc_inverse ys.sum (alpha_binary_prefix ys)) := by
          intro x y xs ys hx hxs hs hlt hNx hNy
          have hne : xs ≠ [] := by rintro rfl; simp at hs; omega
          have hlow := alpha_lexical_lt_iff_inverse_prefix_low xs hne hxs
          set S := xs.sum
          set T := ys.sum
          have hTS : T + 1 ≤ S := by omega
          have hM1 : 2 ^ S * 2 ^ x = 2 ^ (x + S) := by rw [← pow_add, add_comm]
          have hM2 : 2 ^ T * 2 ^ y = 2 ^ (x + S) := by rw [← pow_add, hs, add_comm]
          have hS1 : 2 ^ S = 2 * 2 ^ (S - 1) := by rw [← pow_succ']; congr 1; omega
          have hT1 : 2 ^ T ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hx1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
          have hy1 : 1 ≤ 2 ^ y := Nat.one_le_two_pow
          rw [Nat.mul_sub, Nat.mul_sub, mul_one, mul_one, hM1, hM2]
          have : 2 ^ S ≤ 2 ^ (x + S) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have : 2 ^ T ≤ 2 ^ (x + S) := by omega
          omega
        rcases lt_or_gt_of_ne hxy with h | h
        · simp only [h, true_iff]
          exact key x y xs ys hx hxs hs' h hNx hNy
        · have := key y x ys xs hy hys hs'.symm h hNy hNx
          simp only [show ¬ x < y by omega, false_iff, not_lt]
          exact this.le

theorem alpha_lexical_lt_iff_inverse_prefix (a b : List ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : ∀ v ∈ b, 0 < v) (hs : a.sum = b.sum) : alpha_lexical_lt a b ↔ brgc_inverse a.sum (alpha_binary_prefix a) < brgc_inverse b.sum (alpha_binary_prefix b) :=
  alpha_lexical_lt_iff_inverse_prefix_aux _ a b le_rfl ha hb hs
