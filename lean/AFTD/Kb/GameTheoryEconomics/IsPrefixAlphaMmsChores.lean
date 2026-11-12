import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores

/-!
# is_prefix_alpha_mms_chores

Topic: fair_division   Node: dada5940a84f

Provenance: original. Related work: arXiv:2505.24321

An allocation σ of m chores between two agents is α-MMS after every prefix if for every k with 1 ≤ k ≤ m, the restriction of σ to the first k chores is α-MMS for the first k chores.
-/

/-- An allocation of m chores is alpha-MMS after every prefix if for every prefix length 1 <= k <= m, the restriction of the allocation is alpha-MMS for the restriction of the cost functions. -/
def is_prefix_alpha_mms_chores (m : ℕ) (α : ℝ) (c : Fin 2 → Fin m → ℝ) (σ : Fin m → Fin 2) : Prop :=
  ∀ (k : ℕ) (_ : 1 ≤ k) (hkm : k ≤ m),
    is_alpha_mms_chores α
      (fun i (s : Fin k) => c i ⟨s.val, lt_of_lt_of_le s.isLt hkm⟩)
      (fun (s : Fin k) => σ ⟨s.val, lt_of_lt_of_le s.isLt hkm⟩)
