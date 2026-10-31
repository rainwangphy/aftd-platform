import AFTD.Prelude

/-!
# cycle_cover_difference_cycle_factor_two_word

Topic: graphs   Node: 0747af272263

Provenance: helper lemma. step towards simple_graph_normalized_hop_group_quadratic_word_diameter

If p and q are cycle covers of a relation R, then every cycle factor of p⁻¹ q is a product of at most two letters, each a cycle cover or the inverse of one.
-/

/-- Cycle factors of p⁻¹q for cycle covers p, q are two-letter words (cycle surgery for covers). -/
theorem cycle_cover_difference_cycle_factor_two_word {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (p q r : Equiv.Perm V) (hp : ∀ v, R v (p v)) (hq : ∀ v, R v (q v))
    (hr : r ∈ (p⁻¹ * q).cycleFactorsFinset) :
    ∃ w : List (Equiv.Perm V),
      (∀ x ∈ w, (∀ v, R v (x v)) ∨ (∀ v, R (x v) v)) ∧ w.length ≤ 2 ∧ w.prod = r := by
  have hr_prop := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hr).2
  have h_inj : Function.Injective (fun v => if v ∈ r.support then q v else p v) := by
    intro x y h
    dsimp only at h
    by_cases hx : x ∈ r.support <;> by_cases hy : y ∈ r.support
    · simp only [hx, hy, if_true] at h
      exact q.injective h
    · simp only [hx, hy, if_true, if_false] at h
      exfalso
      have hrx : r x = (p⁻¹ * q) x := hr_prop x hx
      have h1 : p (r x) = q x := by
        rw [hrx, Equiv.Perm.mul_apply]
        simp
      have h2 : p (r x) = p y := by rw [h1, h]
      have h3 : r x = y := p.injective h2
      have hsupp : r x ∈ r.support := Equiv.Perm.apply_mem_support.mpr hx
      rw [h3] at hsupp
      exact hy hsupp
    · simp only [hx, hy, if_true, if_false] at h
      exfalso
      have hry : r y = (p⁻¹ * q) y := hr_prop y hy
      have h1 : p (r y) = q y := by
        rw [hry, Equiv.Perm.mul_apply]
        simp
      have h2 : p (r y) = p x := by rw [h1, ← h]
      have h3 : r y = x := p.injective h2
      have hsupp : r y ∈ r.support := Equiv.Perm.apply_mem_support.mpr hy
      rw [h3] at hsupp
      exact hx hsupp
    · simp only [hx, hy, if_false] at h
      exact p.injective h
  let A : Equiv.Perm V := Equiv.ofBijective (fun v => if v ∈ r.support then q v else p v)
    (Finite.injective_iff_bijective.mp h_inj)
  have hA_apply (v : V) : A v = if v ∈ r.support then q v else p v := Equiv.ofBijective_apply _ _ _
  refine ⟨[p⁻¹, A], ?_, by simp, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · right
      intro v
      have h := hp (p⁻¹ v)
      simpa using h
    · left
      intro v
      rw [hA_apply]
      split_ifs with hv
      · exact hq v
      · exact hp v
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    ext v
    rw [Equiv.Perm.mul_apply, hA_apply]
    by_cases hv : v ∈ r.support
    · simp only [hv, if_true]
      have hrx := hr_prop v hv
      rw [hrx, Equiv.Perm.mul_apply]
    · simp only [hv, if_false]
      rw [Equiv.Perm.notMem_support.mp hv]
      simp
