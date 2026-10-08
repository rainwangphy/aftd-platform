import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordListDecodable

/-!
# ErrorCorrectingCodes.Codeword.exists_listDecodable_code

Topic: information   Node: 8c7a53740cb5

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.exists_listDecodable_code`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/ListDecoding.lean (Apache-2.0); 1 verbatim; compiled here.

Existence of list-decodable codes. Let $\alpha$ be a finite field, and fix natural numbers $n$, $L$, $M$ and a real number
$p$ with $0 \le p \le 1$, $1 \le L$, $L < M$, and $M \le \abs{\alpha}^n$. Suppose $V$ is
a natural number bounding the volume of every Hamming ball of radius $\lfloor
pn\rfloor$, in the sense that each such ball around an arbitrary word $y \in \alpha^n$
contains at most $V$ codewords, and suppose that
\[
\abs{\alpha}^n \cdot \binom{V}{L+1} \cdot \binom{\abs{\alpha}^n - (L+1)}{\,M-(L+1)\,}
\;<\; \binom{\abs{\alpha}^n}{M}.
\]
Then there exists a code $C$ of length $n$ over $\alpha$ consisting of exactly $M$
codewords that is $(p,L)$-list-decodable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Existence of list-decodable codes**: if the ball volume `V` and code size `M` satisfy the given counting inequality, then there exists a code `C` of size `M` that is `(p, L)`-list-decodable. -/
lemma ErrorCorrectingCodes.Codeword.exists_listDecodable_code (n L M : ℕ) (p : ℝ)
  (hp1 : 0 ≤ p) (hp2 : p ≤ 1) (hL : 1 ≤ L)
  (V : ℕ)
  (hV : ∀ y : Codeword n α, (hamming_ball (Nat.floor (p*n)) y).card ≤ V)
  (h_ineq : (Fintype.card α)^n * (Nat.choose V (L+1)) * (Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1))) < Nat.choose ((Fintype.card α)^n) M)
  (hM_le_N : M ≤ (Fintype.card α)^n)
  (hL_lt_M : L < M) :
  ∃ C : Code n α, C.card = M ∧ list_decodable p hp1 hp2 n L hL C := by
    contrapose h_ineq;
    have h_bad_codes : ∀ y : Codeword n α, (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ Nat.choose V (L + 1) * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
      intro y
      have h_bad_codes_y : (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Finset.powersetCard (L + 1) (hamming_ball ⌊p * n⌋₊ y)).card * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.biUnion ( Finset.powersetCard ( L + 1 ) ( hamming_ball ⌊p * n⌋₊ y ) ) fun S => Finset.image ( fun T => S ∪ T ) ( Finset.powersetCard ( M - ( L + 1 ) ) ( Finset.univ \ S ) );
        · intro C hC; simp_all +decide [ Finset.subset_iff ] ;
          obtain ⟨ S, hS ⟩ := Finset.exists_subset_card_eq hC.2;
          refine' ⟨ S, ⟨ fun x hx => _, hS.2 ⟩, C \ S, ⟨ fun x hx => _, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          grind;
        · refine' le_trans ( Finset.card_biUnion_le ) _;
          refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.card_image_le ) _;
          simp +decide [ Finset.card_sdiff ];
          refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.choose_le_choose _ _ ) _;
          rotate_left;
          use fun x => Fintype.card α ^ n - ( L + 1 );
          · simp +decide [ Finset.card_powersetCard ];
          · grind;
      refine' le_trans h_bad_codes_y _;
      exact Nat.mul_le_mul_right _ ( by rw [ Finset.card_powersetCard ] ; exact Nat.choose_le_choose _ ( hV y ) );
    have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Fintype.card α) ^ n * Nat.choose V (L + 1) * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
      have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (∑ y : Codeword n α, (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card) := by
        have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Finset.biUnion (Finset.univ : Finset (Codeword n α)) (fun y => Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α))))).card := by
          exact Finset.card_le_card fun x hx => by aesop;
        exact h_bad_codes_count.trans ( Finset.card_biUnion_le );
      refine' le_trans h_bad_codes_count ( le_trans ( Finset.sum_le_sum fun _ _ => h_bad_codes _ ) _ );
      simp +decide [ mul_assoc, Fintype.card_pi ];
    simp_all +decide [ list_decodable ];
    refine' le_trans _ h_bad_codes_count;
    rw [ Finset.filter_true_of_mem ];
    · simp +decide [ Finset.card_univ ];
    · intro C hC; specialize h_ineq C; aesop;
