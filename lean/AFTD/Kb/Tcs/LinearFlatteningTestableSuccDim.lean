import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_testable_succ_dim

Topic: algebraic_complexity   Node: 99287db5c85c

Provenance: helper lemma. step towards linear_flattening_testable_even_step

Testability is monotone in the tensor dimension at fixed order: if a linear flattening on (ℂⁿ)⊗³ has potency greater than r, then so does one on (ℂ^{n+1})⊗³, obtained by restricting a tensor to its first n coordinates in each mode.
-/

def linear_flattening_testable_succ_dim_restrict {n : ℕ} :
    (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin n → Fin n → Fin n → ℂ) where
  toFun A i j k := A i.castSucc j.castSucc k.castSucc
  map_add' A B := by ext i j k; rfl
  map_smul' c A := by ext i j k; rfl

def linear_flattening_testable_succ_dim_pad {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ :=
  fun i j k => Fin.lastCases (0 : ℂ) (fun a => Fin.lastCases (0 : ℂ) (fun b => Fin.lastCases (0 : ℂ) (fun c => T a b c) k) j) i

/-- Padding a flattening by a coordinate preserves its potency at fixed order; note it never raises the order, since every pure-tensor image of the small flattening is already a pure-tensor image of the padded one. -/
theorem linear_flattening_testable_succ_dim {n r : ℕ}
    (h : linear_flattening_testable n r) : linear_flattening_testable (n + 1) r := by
  rcases h with ⟨u, v, L, T, hT⟩
  refine ⟨u, v, L.comp linear_flattening_testable_succ_dim_restrict, linear_flattening_testable_succ_dim_pad T, ?_⟩
  intro x y z
  have hq_pure : linear_flattening_testable_succ_dim_restrict (tensor3_pure x y z) =
      tensor3_pure (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => z i.castSucc) := by
    ext i j k
    simp [linear_flattening_testable_succ_dim_restrict, tensor3_pure]
  have hq_pad : linear_flattening_testable_succ_dim_restrict (linear_flattening_testable_succ_dim_pad T) = T := by
    ext i j k
    simp [linear_flattening_testable_succ_dim_restrict, linear_flattening_testable_succ_dim_pad, Fin.lastCases_castSucc]
  change r * (L (linear_flattening_testable_succ_dim_restrict (tensor3_pure x y z))).rank <
    (L (linear_flattening_testable_succ_dim_restrict (linear_flattening_testable_succ_dim_pad T))).rank
  rw [hq_pure, hq_pad]
  exact hT _ _ _
