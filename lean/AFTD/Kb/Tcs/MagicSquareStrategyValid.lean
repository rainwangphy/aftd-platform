import AFTD.Prelude
import AFTD.Kb.Tcs.IsPovm

/-!
# magic_square_strategy_valid

Topic: quantum   Node: a63461f206d7

Provenance: formalization of a published result. Source: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 5 (the full magic-square game; finite-dimensional tensor-product strategies with arbitrary POVMs and quantum side information).

Given dA dB dE : ℕ, Alice's effects A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ (A x s: row x, then answer s), Bob's effects B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ (B j c: column j, then answer c), and a complex matrix ρ indexed by the product type (Fin dA × Fin dB) × Fin dE (the state on Alice, Bob and the adversary Eve, left-associated): magic_square_strategy_valid A B ρ holds iff (1) for every row x, A x is a POVM (is_povm dA (A x)); (2) A x s = 0 whenever xor (xor (s 0) (s 1)) (s 2) = true (true encodes the sign -1, so Alice's legal answers have sign product +1); (3) for every column j, B j is a POVM (is_povm dB (B j)); (4) for every column j, B j c = 0 whenever xor (xor (c 0) (c 1)) (c 2) = false (Bob's legal answers have sign product -1); (5) ρ is positive semidefinite with trace 1. This is a finite-dimensional tensor-product strategy for the magic-square game with quantum side information: Alice (dimension dA) has, for each row x in {0,1,2}, a POVM whose outcomes are sign strings of length 3 with product +1 (an even number of -1 signs); Bob (dimension dB) has, for each column j, a POVM whose outcomes are sign strings with product -1; and the shared state is a density matrix (positive semidefinite, trace one) on the tensor product of Alice's, Bob's and the adversary Eve's (dimension dE) systems. Sign strings are encoded as Fin 3 → Bool with true meaning -1, and effects on illegal strings are zero.
-/

/-- A finite-dimensional magic-square strategy with quantum side information is valid: Alice's effects `A x s` (row `x`, answer `s`) form, for each row, a POVM supported on the sign strings with an even number of `-1`s (`true` meaning the sign `-1`); Bob's effects `B j c` (column `j`, answer `c`) form, for each column, a POVM supported on the sign strings with an odd number of `-1`s; and `ρ` is a density matrix on `(A ⊗ B) ⊗ E`, `E` being the adversary's system. -/
def magic_square_strategy_valid {dA dB dE : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ) : Prop := open scoped ComplexOrder in
  (∀ x, is_povm dA (A x)) ∧
  (∀ x s, xor (xor (s 0) (s 1)) (s 2) = true → A x s = 0) ∧
  (∀ j, is_povm dB (B j)) ∧
  (∀ j c, xor (xor (c 0) (c 1)) (c 2) = false → B j c = 0) ∧
  ρ.PosSemidef ∧ ρ.trace = 1
