import AFTD.Prelude

/-!
# op309_triangle_free_class_cycle_budget

Topic: combinatorics   Node: f328ea442ce3

Provenance: helper lemma. OP-309 high-girth port-class incidence route, IN-1099.

For a family of connected class supports, if each cyclic support uses at least four edges and twice its cycle rank is at most its branch count plus two, then a total branch budget of twice s and total edge budget k bound the sum of cycle ranks by s plus floor(k/4).
-/

theorem op309_triangle_free_class_cycle_budget {ι : Type*} [Fintype ι] (cyc branch edges : ι → ℕ) (s k : ℕ) (hlocal : ∀ i, 2 * cyc i ≤ branch i + 2 * (if cyc i = 0 then 0 else 1)) (hsize : ∀ i, 4 * (if cyc i = 0 then 0 else 1) ≤ edges i) (hbranch : ∑ i, branch i ≤ 2*s) (hedges : ∑ i, edges i ≤ k) : ∑ i, cyc i ≤ s + k/4 := by
  classical
  have h₁ : ∑ i, (2 * cyc i) ≤ ∑ i, (branch i + 2 * (if cyc i = 0 then 0 else 1)) := Finset.sum_le_sum fun i _ => hlocal i
  have h₂ : ∑ i, (4 * (if cyc i = 0 then 0 else 1)) ≤ ∑ i, edges i := Finset.sum_le_sum fun i _ => hsize i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h₁ h₂
  omega
