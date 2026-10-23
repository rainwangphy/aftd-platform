import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber

/-!
# simple_graph_equivalence_covering_number_cycle_power_ge

Topic: combinatorics   Node: 3366dd46f5a5

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Lemma 2.2 (the lower bound of Theorem 1.2).

For k ≥ 1 and n ≥ 2k + 2, eq(C_n^k) ≥ 1 + ⌈log₂(k + 1)⌉.
-/

/-- Vertices at forward distance `d ∈ [1, k]` are adjacent in `C_n^k`. -/
theorem simple_graph_equivalence_covering_number_cycle_power_ge_adj (n k : ℕ) [NeZero n]
    (u : ZMod n) (d : ℕ) (hd1 : 1 ≤ d) (hdk : d ≤ k) (hdn : d < n) :
    (simple_graph_cycle_power n k).Adj u (u + (d : ZMod n)) := by
  have hval : ((d : ZMod n)).val = d := ZMod.val_cast_of_lt hdn
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : (d : ZMod n) = 0 := by linear_combination -h
    rw [h0, ZMod.val_zero] at hval
    omega
  · have h1 : (u + (d : ZMod n)) - u = (d : ZMod n) := by ring
    rw [h1, hval]
    exact min_le_of_right_le hdk

/-- Vertices at forward distance `k + 1` are distinct and not adjacent in `C_n^k`
when `n ≥ 2k + 2`. -/
theorem simple_graph_equivalence_covering_number_cycle_power_ge_nadj (n k : ℕ) [NeZero n]
    (hn : 2 * k + 2 ≤ n) (u : ZMod n) :
    u ≠ u + ((k + 1 : ℕ) : ZMod n) ∧
      ¬ (simple_graph_cycle_power n k).Adj u (u + ((k + 1 : ℕ) : ZMod n)) := by
  have hval : (((k + 1 : ℕ) : ZMod n)).val = k + 1 := ZMod.val_cast_of_lt (by omega)
  have hnz : NeZero (((k + 1 : ℕ) : ZMod n)) :=
    ⟨fun h => by rw [h, ZMod.val_zero] at hval; omega⟩
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ((k + 1 : ℕ) : ZMod n) = 0 := by linear_combination -h
    exact hnz.out h0
  · rintro ⟨-, hmin⟩
    have h1 : (u + ((k + 1 : ℕ) : ZMod n)) - u = ((k + 1 : ℕ) : ZMod n) := by ring
    have h2 : u - (u + ((k + 1 : ℕ) : ZMod n)) = -((k + 1 : ℕ) : ZMod n) := by ring
    rw [h1, h2, ZMod.val_neg_of_ne_zero, hval] at hmin
    omega

/-- Every finite simple graph has an equivalence cover (one class per ordered pair). -/
theorem simple_graph_equivalence_covering_number_cycle_power_ge_exists {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    simple_graph_has_equivalence_cover G (Fintype.card (V × V)) := by
  classical
  let e := Fintype.equivFin (V × V)
  refine ⟨fun s w => if G.Adj (e.symm s).1 (e.symm s).2 ∧ w = (e.symm s).2 then (e.symm s).1
    else w, ?_, ?_⟩
  · intro s u v huv h
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact absurd (h1.2.trans h2.2.symm) huv
    · rw [h1.2, ← h]; exact h1.1.symm
    · rw [h2.2, h]; exact h2.1
    · exact absurd h huv
  · intro u v huv
    refine ⟨e (u, v), ?_⟩
    simp [huv, huv.ne]

/-- The rank bound: a cover of `C_n^k` (`n ≥ 2k + 2`) by `t` equivalence subgraphs
has `2k + 2 ≤ 2^t`. -/
theorem simple_graph_equivalence_covering_number_cycle_power_ge_bound (n k : ℕ) (hk : 1 ≤ k)
    (hn : 2 * k + 2 ≤ n) [NeZero n] (t : ℕ) (c : Fin t → ZMod n → ZMod n)
    (hc1 : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n k).Adj u v)
    (hc2 : ∀ u v, (simple_graph_cycle_power n k).Adj u v → ∃ s, c s u = c s v) :
    2 * k + 2 ≤ 2 ^ t := by
  classical
  have ht : 1 ≤ t := by
    obtain ⟨s, -⟩ := hc2 0 (0 + ((1 : ℕ) : ZMod n))
      (simple_graph_equivalence_covering_number_cycle_power_ge_adj n k 0 1 le_rfl hk (by omega))
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact s.elim0)
  set phi : ZMod n → ZMod n → ℚ :=
    fun u v => ∏ s : Fin t, (((c s u).val : ℚ) - ((c s v).val : ℚ)) with hphi
  have hphi0 : ∀ u v, (u = v ∨ (simple_graph_cycle_power n k).Adj u v) → phi u v = 0 := by
    intro u v h
    have hs : ∃ s, c s u = c s v := by
      rcases h with rfl | h
      · exact ⟨⟨0, ht⟩, rfl⟩
      · exact hc2 u v h
    obtain ⟨s, hs⟩ := hs
    simp only [hphi]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, sub_self])
  have hphine : ∀ u v, u ≠ v → ¬ (simple_graph_cycle_power n k).Adj u v → phi u v ≠ 0 := by
    intro u v hne hna
    simp only [hphi]
    rw [Finset.prod_ne_zero_iff]
    intro s _ h
    apply hna
    apply hc1 s u v hne
    apply ZMod.val_injective
    exact_mod_cast sub_eq_zero.mp h
  let x : Fin (2 * k + 2) → ZMod n := fun i => ((i.val : ℕ) : ZMod n)
  let y : Fin (2 * k + 2) → ZMod n := fun j => ((j.val + k + 1 : ℕ) : ZMod n)
  let M : Matrix (Fin (2 * k + 2)) (Fin (2 * k + 2)) ℚ := fun i j => phi (x i) (y j)
  have hdiag : ∀ i, M i i ≠ 0 := by
    intro i
    have hy : y i = x i + ((k + 1 : ℕ) : ZMod n) := by
      simp only [x, y]
      push_cast
      ring
    have hh := simple_graph_equivalence_covering_number_cycle_power_ge_nadj n k hn (x i)
    rw [← hy] at hh
    exact hphine _ _ hh.1 hh.2
  have htri : M.BlockTriangular id := by
    intro i j hji
    simp only [id] at hji
    rw [Fin.lt_def] at hji
    have hi := i.isLt
    have hj := j.isLt
    apply hphi0
    by_cases hle : i.val ≤ j.val + k + 1
    · have hy : y j = x i + ((j.val + k + 1 - i.val : ℕ) : ZMod n) := by
        simp only [x, y]
        rw [← Nat.cast_add]
        congr 1
        omega
      by_cases hd : j.val + k + 1 - i.val = 0
      · left
        rw [hy, hd]
        simp
      · right
        rw [hy]
        exact simple_graph_equivalence_covering_number_cycle_power_ge_adj n k _ _
          (by omega) (by omega) (by omega)
    · have hx : x i = y j + ((i.val - (j.val + k + 1) : ℕ) : ZMod n) := by
        simp only [x, y]
        rw [← Nat.cast_add]
        congr 1
        omega
      right
      rw [hx]
      exact (simple_graph_equivalence_covering_number_cycle_power_ge_adj n k _ _
        (by omega) (by omega) (by omega)).symm
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  have hrank : M.rank = 2 * k + 2 := by
    rw [Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).mpr
      (isUnit_iff_ne_zero.mpr hdet))]
    simp
  let U : Matrix (Fin (2 * k + 2)) (Finset (Fin t)) ℚ :=
    fun i S => ∏ s ∈ S, ((c s (x i)).val : ℚ)
  let W : Matrix (Finset (Fin t)) (Fin (2 * k + 2)) ℚ :=
    fun S j => ∏ s ∈ Finset.univ \ S, (-((c s (y j)).val : ℚ))
  have hMUW : M = U * W := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [M, U, W, hphi]
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_add, Finset.powerset_univ]
  have h1 := Matrix.rank_mul_le_left U W
  have h2 := Matrix.rank_le_card_width U
  rw [← hMUW, hrank] at h1
  simpa [Fintype.card_finset] using h1.trans h2

theorem simple_graph_equivalence_covering_number_cycle_power_ge (n k : ℕ) (hk : 1 ≤ k)
    (hn : 2 * k + 2 ≤ n) :
    1 + Nat.clog 2 (k + 1) ≤
      simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) := by
  classical
  have : NeZero n := ⟨by omega⟩
  unfold simple_graph_equivalence_covering_number
  apply le_csInf
  · exact ⟨_, simple_graph_equivalence_covering_number_cycle_power_ge_exists _⟩
  · rintro t ⟨c, hc1, hc2⟩
    have hb := simple_graph_equivalence_covering_number_cycle_power_ge_bound n k hk hn t c hc1 hc2
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hb
      · exact h
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    have : Nat.clog 2 (k + 1) ≤ m := by
      apply Nat.clog_le_of_le_pow
      rw [pow_succ] at hb
      omega
    omega
