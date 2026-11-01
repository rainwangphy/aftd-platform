import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# grid_arrangement_column_deviation_subset_sum_le

Topic: combinatorics   Node: 5075a26c2f4a

Provenance: helper lemma. arXiv:2610.38386 Lemma 3.8

For any grid arrangement $S$ of order $n \ge 3$ and any column subset $J$ of cardinality $p$, the column-deviation sum $\sum_{j \in J} \gamma_j$ is bounded above by $pn(N-pn)/2$.
-/

/-- Upper bound for column-deviation subset sum by the sum of the largest entries. -/
theorem grid_arrangement_column_deviation_subset_sum_le
    {n : ℕ} (hn : 3 ≤ n) (S : Fin n × Fin n → ℤ)
    (hS_inj : Function.Injective S)
    (hS_range : ∀ c, 1 ≤ S c ∧ S c ≤ (n : ℤ) ^ 2)
    (J : Finset (Fin n)) :
    let γ := fun j => (∑ i : Fin n, S (i, j)) - (n : ℤ) * ((n : ℤ) ^ 2 + 1) / 2
    let p := J.card
    let N := (n : ℤ) ^ 2
    ∑ j ∈ J, γ j ≤ (p : ℤ) * (n : ℤ) * (N - (p : ℤ) * (n : ℤ)) / 2 := by
  dsimp only
  have hmaxsum : ∀ (B : ℕ) (T : Finset ℤ),
      (∀ x ∈ T, 1 ≤ x ∧ x ≤ (B : ℤ)) →
      ∑ x ∈ T, x ≤ (T.card : ℤ) * (2 * (B : ℤ) - (T.card : ℤ) + 1) / 2 := by
    intro B T hT
    induction B generalizing T with
    | zero =>
      have hTe : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have h := hT x hx
        omega
      subst hTe
      simp
    | succ B ih =>
      by_cases hmem : ((B : ℤ) + 1) ∈ T
      · have hcard_ge : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hmem⟩
        have hT' : ∀ x ∈ T.erase ((B:ℤ)+1), 1 ≤ x ∧ x ≤ (B:ℤ) := by
          intro x hx
          simp only [Finset.mem_erase] at hx
          have h := hT x hx.2
          refine ⟨h.1, ?_⟩
          rw [Nat.cast_succ] at h
          omega
        have key := ih (T.erase ((B:ℤ)+1)) hT'
        rw [Finset.card_erase_of_mem hmem, Nat.cast_sub hcard_ge, Nat.cast_one] at key
        have hsum : ∑ x ∈ T.erase ((B:ℤ)+1), x + ((B:ℤ)+1) = ∑ x ∈ T, x :=
          Finset.sum_erase_add _ _ hmem
        rw [← hsum]
        push_cast
        have hb : (T.card : ℤ) * (2 * ((B : ℤ) + 1) - (T.card : ℤ) + 1)
            = ((T.card : ℤ) - 1) * (2 * (B : ℤ) - ((T.card : ℤ) - 1) + 1) + ((B:ℤ)+1) * 2 := by
          ring
        rw [hb, Int.add_mul_ediv_right _ _ (by norm_num : (2:ℤ) ≠ 0)]
        linarith [key]
      · have hT' : ∀ x ∈ T, 1 ≤ x ∧ x ≤ (B:ℤ) := by
          intro x hx
          have h := hT x hx
          refine ⟨h.1, ?_⟩
          rw [Nat.cast_succ] at h
          by_contra hc
          push Not at hc
          have : x = (B:ℤ)+1 := by omega
          exact hmem (this ▸ hx)
        have key := ih T hT'
        push_cast
        have hb : (T.card : ℤ) * (2 * ((B : ℤ) + 1) - (T.card : ℤ) + 1)
            = (T.card : ℤ) * (2 * (B : ℤ) - (T.card : ℤ) + 1) + (T.card : ℤ) * 2 := by
          ring
        rw [hb, Int.add_mul_ediv_right _ _ (by norm_num : (2:ℤ) ≠ 0)]
        have hnn : (0:ℤ) ≤ (T.card : ℤ) := by positivity
        linarith [key]
  have harith : ∀ (m p : ℤ),
      (p*m) * (2*m^2 - p*m + 1) / 2 - p*(m*(m^2+1)/2) = p*m*(m^2 - p*m)/2 := by
    intro m p
    have hB : (2:ℤ) ∣ m*(m^2+1) := by
      rcases Int.even_or_odd m with h | h
      · obtain ⟨k, hk⟩ := h
        exact ⟨k*(m^2+1), by rw [hk]; ring⟩
      · obtain ⟨k, hk⟩ := h
        exact ⟨m*(2*k^2+2*k+1), by rw [hk]; ring⟩
    have hBhalf : 2*(m*(m^2+1)/2) = m*(m^2+1) := Int.mul_ediv_cancel' hB
    have hA : (p*m)*(2*m^2 - p*m+1) = p*m*(m^2-p*m) + p*(m*(m^2+1)) := by ring
    have hpB : p*(m*(m^2+1)) = (p*(m*(m^2+1)/2))*2 := by
      calc p*(m*(m^2+1)) = p*(2*(m*(m^2+1)/2)) := by rw [hBhalf]
        _ = (p*(m*(m^2+1)/2))*2 := by ring
    rw [hA, hpB, Int.add_mul_ediv_right _ _ (by norm_num : (2:ℤ) ≠ 0)]
    ring
  set C : Finset (Fin n × Fin n) := Finset.univ ×ˢ J with hCdef
  set T : Finset ℤ := C.image S with hTdef
  have hInj : Set.InjOn S ↑C := fun a _ b _ h => hS_inj h
  have hCcard : C.card = n * J.card := by
    rw [hCdef, Finset.card_product]; simp
  have hTcard : T.card = n * J.card := by
    rw [hTdef, Finset.card_image_of_injOn hInj, hCcard]
  have hTbound : ∀ x ∈ T, 1 ≤ x ∧ x ≤ ((n^2 : ℕ) : ℤ) := by
    intro x hx
    rw [hTdef, Finset.mem_image] at hx
    obtain ⟨c, hc, hcS⟩ := hx
    rw [← hcS]
    obtain ⟨h1, h2⟩ := hS_range c
    refine ⟨h1, ?_⟩
    push_cast
    exact h2
  have hmax := hmaxsum (n^2) T hTbound
  have hTsum : ∑ x ∈ T, x = ∑ c ∈ C, S c := by
    rw [hTdef]; exact Finset.sum_image hInj
  have hcol : ∑ c ∈ C, S c = ∑ j ∈ J, ∑ i : Fin n, S (i, j) := by
    rw [hCdef, Finset.sum_product, Finset.sum_comm]
  have hbound1 : ∑ c ∈ C, S c ≤ ((J.card:ℤ)*(n:ℤ)) * (2*((n:ℤ)^2) - ((J.card:ℤ)*(n:ℤ)) + 1) / 2 := by
    rw [← hTsum]
    have e1 : (T.card : ℤ) = (J.card:ℤ)*(n:ℤ) := by rw [hTcard]; push_cast; ring
    have e2 : ((n^2:ℕ):ℤ) = (n:ℤ)^2 := by push_cast; ring
    rw [e1, e2] at hmax
    exact hmax
  have hgamma : ∑ j ∈ J, ((∑ i : Fin n, S (i,j)) - (n:ℤ)*((n:ℤ)^2+1)/2)
      = (∑ c ∈ C, S c) - (J.card:ℤ)*((n:ℤ)*((n:ℤ)^2+1)/2) := by
    rw [Finset.sum_sub_distrib, ← hcol, Finset.sum_const, nsmul_eq_mul]
  rw [hgamma]
  have hfe := harith (n:ℤ) (J.card:ℤ)
  linarith [hbound1, hfe]
