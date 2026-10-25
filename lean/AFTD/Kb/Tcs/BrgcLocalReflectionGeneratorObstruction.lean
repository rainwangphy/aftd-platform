import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordInjective
import AFTD.Kb.Tcs.BitwordRotate

/-!
# brgc_local_reflection_generator_obstruction

Topic: combinatorics   Node: 41a9efe6f469

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Two strict maximum-rank primitive generators whose proposed local generator reflection is not maximum-rank; an obstruction to a naive proof route, not a refutation of OP-392.
-/

def brgc_reflection_certificate_a : List ℕ := [219541,85205,170411,183465,157357,209573,105141,210283,103721,207443,109401,218803,86681,173363,177561,169165,185957,152373]
def brgc_reflection_certificate_b : List ℕ := [878165,340821,681643,733865,629421,838309,420533,841067,415017,830035,437081,874163,348825,697651,701849,693453,710245,676661,743829,609493]

theorem brgc_strict_rotation_max_of_certificate (n t : ℕ) (ranks : List ℕ)
    (h : ∀ k : Fin n,
      brgc_word (ranks.getD k.val 0) = (bitword_rotate n)^[k.val] (brgc_word t) ∧
      (k.val ≠ 0 → ranks.getD k.val 0 < t)) :
    ∀ k : Fin n, k.val ≠ 0 → ∀ s,
      brgc_word s = (bitword_rotate n)^[k.val] (brgc_word t) → s < t := by
  intro k hk s hs
  have he : s = ranks.getD k.val 0 :=
    brgc_word_injective (hs.trans (h k).1.symm)
  rw [he]
  exact (h k).2 hk

theorem brgc_local_reflection_generator_obstruction :
    (∀ k : Fin 18, k.val ≠ 0 → ∀ s,
      brgc_word s = (bitword_rotate 18)^[k.val] (brgc_word 219541) → s < 219541) ∧
    (∀ k : Fin 20, k.val ≠ 0 → ∀ s,
      brgc_word s = (bitword_rotate 20)^[k.val] (brgc_word 878165) → s < 878165) ∧
    ((775551 : ℕ) ^^^ 2 ^ (20 - 18) ^^^ 1 = 775546) ∧
    (brgc_word 219541 = 193887) ∧
    (brgc_word 878165 = 775551) ∧
    (brgc_word 878163 = 775546) ∧
    (brgc_word 878259 = (bitword_rotate 20)^[11] (brgc_word 878163)) ∧
    878163 < (878259 : ℕ) ∧
    (((193887 : ℕ) ^^^ 1) * 2 ^ 23 / (2 ^ 18 - 1) = 6204375) ∧
    (((775551 : ℕ) ^^^ 1) * 2 ^ 23 / (2 ^ 20 - 1) = 6204405) ∧
    (brgc_word 7025306 = 6204375) ∧
    (brgc_word 7025317 = (6204375 : ℕ) ^^^ 2 ^ (23 - 18)) ∧
    (brgc_word 7025318 = 6204405) ∧
    (brgc_word 7025321 = (6204405 : ℕ) ^^^ 2 ^ (23 - 20)) ∧
    (7025306 % 2 = 0) ∧ (7025318 % 2 = 0) ∧
    (2 ^ 23 - 1 - 7025317 = (1363290 : ℕ)) ∧
    (2 ^ 23 - 1 - 7025306 = (1363301 : ℕ)) ∧
    (2 ^ 23 - 1 - 7025321 = (1363286 : ℕ)) ∧
    (2 ^ 23 - 1 - 7025318 = (1363289 : ℕ)) ∧
    (1363289 + 1 = (1363290 : ℕ)) := by
  refine ⟨brgc_strict_rotation_max_of_certificate 18 219541 brgc_reflection_certificate_a (by decide),
    brgc_strict_rotation_max_of_certificate 20 878165 brgc_reflection_certificate_b (by decide), ?_⟩
  decide
