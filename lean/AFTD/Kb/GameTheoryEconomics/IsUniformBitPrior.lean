import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior

/-!
# is_uniform_bit_prior

Topic: mechanism_design   Node: edd266d7de9c

Provenance: original. Related work: arXiv:2606.22226

A real-valued function μ on ι → Bool is a uniform bit prior on k states if it is a bit prior whose support {x | μ x ≠ 0} has cardinality k and which assigns probability 1 / (k : ℝ) to every state in its support.
-/

open Finset in
/-- A probability distribution on {0, 1}^ι is uniform on k states if it is a bit prior whose support has cardinality k and assigns weight 1/k to each point in its support. -/
def is_uniform_bit_prior {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (μ : (ι → Bool) → ℝ) : Prop :=
  is_bit_prior μ ∧
    ((Finset.univ.filter (fun x => μ x ≠ 0)).card = k) ∧
    (∀ x, μ x ≠ 0 → μ x = 1 / (k : ℝ))
