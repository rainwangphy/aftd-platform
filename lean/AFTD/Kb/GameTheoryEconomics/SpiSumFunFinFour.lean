import AFTD.Prelude

/-!
# spi_sum_fun_fin_four

Topic: mechanism_design   Node: ee39c90155c0

A sum over value profiles Fin 4 -> Fin 2 expands into the 16 explicit profiles.
-/

open Finset in
/-- `E[max]` over four independent two-point rewards expands into a sum over the 16 value profiles. -/
lemma spi_sum_fun_fin_four {β : Type*} [AddCommMonoid β] (f : (Fin 4 → Fin 2) → β) :
    ∑ k, f k = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2, f ![a, b, c, d] := by
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Fintype.sum_unique]
  congr 1
