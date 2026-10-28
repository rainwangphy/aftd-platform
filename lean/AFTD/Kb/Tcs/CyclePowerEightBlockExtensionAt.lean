import AFTD.Prelude

/-!
# cycle_power_eight_block_extension_at

Topic: combinatorics   Node: 12974ad14a7f

Provenance: helper lemma. Uniform local structural route for OP-205 / RT-1, following arXiv:2610.15635. The Boolean eight-block extension remains conjectured; the induction result keeps it as an explicit hypothesis. Finite guarded computations are evidence only, and no graph covering value or research advance is claimed.

The local Boolean extension predicate at block size q: for every integer rooted-profile model of radius8q, selected endpoints, parent matchings at4q and6q, exact pair ownership at4q/6q/7q, monotone outer eighths and coverage of every ordinary distance imply monotone outer quarters. Defining this predicate does not assert it for any positive q.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def cycle_power_eight_block_extension_at (q : ℕ) : Prop :=
  ∀ x : ℤ → ℕ → Bool,
    (∀ p, x p 0 = true ∧ x p (8*q-1) = true) →
    (∀ p a, a < 4*q →
      (a < 2*q → x p (a+4*q) = true → x p a = true) ∧
      (2*q ≤ a → x p a = true → x p (a+4*q) = true)) →
    (∀ p a, a < 2*q →
      (a < q → x p (a+6*q) = true → x p a = true) ∧
      (q ≤ a → x p a = true → x p (a+6*q) = true)) →
    (∀ L : ℕ, (L=q ∨ L=2*q ∨ L=4*q) → ∀ v : ℤ,
      (range L).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8*q-L)).toNat) = 1) →
    (∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < q → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 7*q ≤ a → a ≤ b → b < 8*q →
        x p a = true → x p b = true)) →
    (∀ d : ℕ, 1 ≤ d → d < 8*q → ∀ v : ℤ,
      ∃ a : ℕ, a < 8*q-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true) →
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2*q → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 6*q ≤ a → a ≤ b → b < 8*q →
        x p a = true → x p b = true)
