import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorCritical

/-!
# odd_cycle_is_factor_critical

Topic: graphs   Node: 7d70f5e3fbae

Provenance: helper lemma. arXiv:2611.09072 Claw-free minimal factor-critical and bicritical graphs, proof of Theorem 1.4

For every integer n ≥ 1, the odd cycle graph C_{2n+1} is factor-critical.
-/

lemma odd_cycle_is_factor_critical_one_val {n : ℕ} (hn : 1 ≤ n) :
    ((1 : Fin (2 * n + 1)) : ℕ) = 1 := by
  have : NeZero (2 * n + 1) := ⟨by omega⟩
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

lemma odd_cycle_is_factor_critical_ne_v {n : ℕ} (hn : 1 ≤ n) (v u : Fin (2 * n + 1)) (huv : u ≠ v) :
    (if (u - v).val % 2 = 1 then u + 1 else u - 1) ≠ v := by
  have h1 := odd_cycle_is_factor_critical_one_val hn
  have h_ne : u - v ≠ 0 := by
    intro h
    apply huv
    exact sub_eq_zero.mp h
  have h_pos : 1 ≤ (u - v).val := by
    have : (u - v).val ≠ 0 := by
      intro h
      apply h_ne
      ext
      exact h
    omega
  have h_lt : (u - v).val < 2 * n + 1 := (u - v).isLt
  split_ifs with h_odd
  · intro h_eq
    have : (u + 1) - v = 0 := sub_eq_zero.mpr h_eq
    rw [add_sub_right_comm] at this
    have h_val : ((u - v + 1 : Fin (2 * n + 1)) : ℕ) = 0 := by rw [this]; rfl
    rw [Fin.val_add, h1] at h_val
    have h_div : (2 * n + 1) ∣ ((u - v).val + 1) := Nat.dvd_of_mod_eq_zero h_val
    have h_le : 2 * n + 1 ≤ (u - v).val + 1 := Nat.le_of_dvd (by omega) h_div
    have h_eq' : (u - v).val = 2 * n := by omega
    have h_mod : (u - v).val % 2 = 0 := by rw [h_eq']; omega
    omega
  · intro h_eq
    have : (u - 1) - v = 0 := sub_eq_zero.mpr h_eq
    rw [sub_right_comm] at this
    have : u - v = 1 := sub_eq_zero.mp this
    have h_val : (u - v).val = 1 := by rw [this, h1]
    have : (u - v).val % 2 = 1 := by rw [h_val]
    exact h_odd this

lemma odd_cycle_is_factor_critical_f_f {n : ℕ} (hn : 1 ≤ n) (v u : Fin (2 * n + 1)) (huv : u ≠ v) :
    let f := fun (x : Fin (2 * n + 1)) => if (x - v).val % 2 = 1 then x + 1 else x - 1
    f (f u) = u := by
  intro f
  have h1 := odd_cycle_is_factor_critical_one_val hn
  have h_ne : u - v ≠ 0 := by
    intro h
    apply huv
    exact sub_eq_zero.mp h
  have h_pos : 1 ≤ (u - v).val := by
    have : (u - v).val ≠ 0 := by
      intro h
      apply h_ne
      ext
      exact h
    omega
  have h_lt : (u - v).val < 2 * n + 1 := (u - v).isLt
  by_cases h_odd : (u - v).val % 2 = 1
  · have hfu : f u = u + 1 := by dsimp [f]; rw [if_pos h_odd]
    rw [hfu]
    dsimp [f]
    have h_lt2 : (u - v).val < 2 * n := by
      have : (u - v).val ≤ 2 * n := by omega
      have : (u - v).val ≠ 2 * n := by
        intro heq
        have : (u - v).val % 2 = 0 := by rw [heq]; omega
        omega
      omega
    have h_u'_sub_v : (u + 1) - v = (u - v) + 1 := by rw [add_sub_right_comm]
    have h_val : ((u + 1 - v : Fin (2 * n + 1)) : ℕ) = (u - v).val + 1 := by
      rw [h_u'_sub_v, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega)]
    have h_not_odd : ¬ ((u + 1 - v).val % 2 = 1) := by
      rw [h_val]
      omega
    rw [if_neg h_not_odd]
    exact add_sub_cancel_right u 1
  · have hfu : f u = u - 1 := by dsimp [f]; rw [if_neg h_odd]
    rw [hfu]
    dsimp [f]
    have h_u'_sub_v : (u - 1) - v = (u - v) - 1 := by rw [sub_right_comm]
    have h_val : ((u - 1 - v : Fin (2 * n + 1)) : ℕ) = (u - v).val - 1 := by
      rw [h_u'_sub_v, Fin.val_sub_one_of_ne_zero h_ne]
    have h_is_odd : (u - 1 - v).val % 2 = 1 := by
      rw [h_val]
      omega
    rw [if_pos h_is_odd]
    exact sub_add_cancel u 1

lemma odd_cycle_is_factor_critical_adj {n : ℕ} (hn : 1 ≤ n) (v u : Fin (2 * n + 1)) :
    let f := fun (x : Fin (2 * n + 1)) => if (x - v).val % 2 = 1 then x + 1 else x - 1
    (SimpleGraph.cycleGraph (2 * n + 1)).Adj u (f u) := by
  intro f
  have h1 := odd_cycle_is_factor_critical_one_val hn
  rw [SimpleGraph.cycleGraph_adj']
  dsimp [f]
  split_ifs
  · right
    have : u + 1 - u = 1 := add_sub_cancel_left (u : Fin (2 * n + 1)) 1
    rw [this, h1]
  · left
    have : u - (u - 1) = 1 := sub_sub_cancel u 1
    rw [this, h1]

/-- The odd cycle graph C_{2n+1} is factor-critical for any n ≥ 1. -/
theorem odd_cycle_is_factor_critical (n : ℕ) (hn : 1 ≤ n) :
    IsFactorCritical (SimpleGraph.cycleGraph (2 * n + 1)) := by
  intro v
  let G := SimpleGraph.cycleGraph (2 * n + 1)
  let s : Set (Fin (2 * n + 1)) := {v}ᶜ
  let H := G.induce s
  let f := fun (x : Fin (2 * n + 1)) => if (x - v).val % 2 = 1 then x + 1 else x - 1
  let σ : s → s := fun u => ⟨f u.1, odd_cycle_is_factor_critical_ne_v hn v u.1 u.2⟩
  have h_inv : ∀ x, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    exact odd_cycle_is_factor_critical_f_f hn v x.1 x.2
  have h_adj : ∀ x, H.Adj x (σ x) := by
    intro x
    rw [SimpleGraph.induce_adj]
    exact odd_cycle_is_factor_critical_adj hn v x.1
  let M : H.Subgraph := {
    verts := Set.univ
    Adj := fun x y => y = σ x
    adj_sub := by
      intro x y hxy
      rw [hxy]
      exact h_adj x
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨by
      intro x y hxy
      rw [hxy, h_inv]⟩
  }
  refine ⟨M, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  refine ⟨σ x, rfl, ?_⟩
  intro y hy
  exact hy
