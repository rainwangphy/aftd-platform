import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869BoundedAdversaryOneVertex
import AFTD.Kb.Tcs.Op869BoundedFuelMono
import AFTD.Kb.Tcs.Op869IntegerFoldStageBudget
import AFTD.Kb.Tcs.Op869BoundedInitialVertexMono

/-!
# op869_integer_fold_schedule_conditional

Topic: online_algorithms   Node: 49e0573c4e65

Provenance: helper lemma. Iteration of the fold simulation in arXiv:2610.41516, Lemma 2.5 and Section 2.3; a step toward OP-869.

Assuming the stated fold simulation bound with constant C, the integer schedule m, m squared, up to m to the m forces m to the m colors on any sufficiently large n, with explicit budget F to the m squared and post-degree F to the m, where F is C times K cubed times 2 to the C times (m+1), and K=m to the m.
-/

theorem op869_integer_fold_schedule_conditional (C m : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) (hsim : ∀ n q t K D : ℕ, 1 ≤ t → t ≤ q → q ≤ K → 1 ≤ D → op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) → ∀ n' D' : ℕ, C * K^2 * q * n * D * 2^(C * ((q + t - 1) / t)) ≤ n' → C * K^2 * q * D * 2^(C * ((q + t - 1) / t)) ≤ D' → op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅)) : let K := m^m; let F := C * K^3 * 2^(C * (m+1)); ∀ n : ℕ, F^(m^2) ≤ n → op869_bounded_adversary_forces 3 1 K (F^m) n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) := by
  let K := m^m
  let F := C * K^3 * 2^(C * (m+1))
  change ∀ n : ℕ, F^(m^2) ≤ n →
      op869_bounded_adversary_forces 3 1 K (F^m) n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅)
  have hm0 : 0 < m := by omega
  have hC0 : 0 < C := by omega
  have hF0 : 0 < F := by dsimp [F,K]; positivity
  have hstages : ∀ j : ℕ, j ≤ m →
      op869_bounded_adversary_forces 3 (m^(m-j)) K (F^j) (F^(j^2)) 0
        (fun _ : Fin (F^(j^2)) => ∅) (fun _ : Fin (F^(j^2)) => ∅) := by
    intro j hj
    induction j with
    | zero =>
      change op869_bounded_adversary_forces 3 K K 1 1 0
        (fun _ : Fin 1 => ∅) (fun _ : Fin 1 => ∅)
      exact op869_bounded_adversary_one_vertex (n:=1) (k:=3) (t:=K) (D:=1) (by decide) (by decide)
    | succ j ih =>
      have hjm : j < m := by omega
      have hold := ih (by omega)
      have ht0 : 0 < m^(m-(j+1)) := by positivity
      have hD0 : 0 < F^j := pow_pos hF0 _
      have htq : m^(m-(j+1)) ≤ m^(m-j) :=
        pow_le_pow_right' (by omega : 1 ≤ m) (by omega)
      have hqK : m^(m-j) ≤ K := by
        dsimp [K]
        exact pow_le_pow_right' (by omega : 1 ≤ m) (by omega)
      have hbud := op869_integer_fold_stage_budget C m j hC hm hjm
      have hnew := hsim (F^(j^2)) (m^(m-j)) (m^(m-(j+1))) K (F^j)
        ht0 htq hqK hD0 hold (F^((j+1)^2)) (F^(j+1)) hbud.1 hbud.2
      simpa only [Nat.succ_eq_add_one] using hnew
  intro n hn
  have hlast := hstages m (le_refl m)
  have hlast' : op869_bounded_adversary_forces 3 1 K (F^m) (F^(m^2)) 0
      (fun _ : Fin (F^(m^2)) => ∅) (fun _ : Fin (F^(m^2)) => ∅) := by
    simpa using hlast
  exact op869_bounded_initial_vertex_mono hn 3 1 K (F^m) (by decide) hlast'
