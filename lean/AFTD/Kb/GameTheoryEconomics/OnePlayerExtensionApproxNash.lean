import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NormalFormExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.IsApproxNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.NormalFormSubgameLast
import AFTD.Kb.GameTheoryEconomics.IsPureBestResponseLast
import AFTD.Kb.GameTheoryEconomics.OnePlayerExtensionThetaIdentity
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# one_player_extension_approx_nash

Topic: equilibria   Node: e828a12f115a

Provenance: formalization of a published result. Source: arXiv:2611.06076 Lemma 2.1 -- Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria

In an (r+1)-player normal-form game with payoff functions u : Fin (r + 1) → ((j : Fin (r + 1)) → A j) → ℝ taking values in [0, 1] (satisfying ∀ i a, 0 ≤ u i a ∧ u i a ≤ 1), let α be a real number satisfying 0 ≤ α and α ≤ 1. If x is an α-approximate Nash equilibrium of the r-player subgame fixing player Fin.last r to pure action s : A (Fin.last r), and b : A (Fin.last r) is a pure best response of player Fin.last r to x in the full game, then setting θ = 1/(2-α), the product profile Fin.snoc x (stdSimplex.mix θ _ _ (stdSimplex.pure s) (stdSimplex.pure b)) is a θ-approximate Nash equilibrium of the (r+1)-player game.
-/

open BigOperators

lemma one_player_extension_approx_nash_prod_nonneg {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (x : (j : Fin n) → stdSimplex ℝ (A j)) (a : (j : Fin n) → A j) :
    0 ≤ ∏ j : Fin n, (x j).val (a j) :=
  Finset.prod_nonneg (fun j _ => (x j).2.1 (a j))

lemma one_player_extension_approx_nash_sum_prod_eq_one {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (x : (j : Fin n) → stdSimplex ℝ (A j)) :
    (∑ a : (j : Fin n) → A j, ∏ j : Fin n, (x j).val (a j)) = 1 := by
  have h := @Finset.prod_univ_sum (Fin n) ℝ _ _ A _ (fun _ => Finset.univ) (fun j a => (x j).val a)
  classical
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  have h1 (j : Fin n) : (∑ a : A j, (x j).val a) = 1 := (x j).2.2
  simp_rw [h1, Finset.prod_const_one]

lemma one_player_extension_approx_nash_expected_payoff_le_one {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (u : Fin n → ((i : Fin n) → A i) → ℝ)
    (hu : ∀ i a, 0 ≤ u i a ∧ u i a ≤ 1)
    (i : Fin n) (x : (j : Fin n) → stdSimplex ℝ (A j)) :
    normal_form_expected_payoff u i x ≤ 1 := by
  unfold normal_form_expected_payoff
  have h_le : (∑ a, (∏ j, (x j).val (a j)) * u i a) ≤ ∑ a : (j : Fin n) → A j, (∏ j, (x j).val (a j)) * 1 := by
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left (hu i a).2 (one_player_extension_approx_nash_prod_nonneg x a)
  simp_rw [mul_one] at h_le
  rw [one_player_extension_approx_nash_sum_prod_eq_one] at h_le
  exact h_le

lemma one_player_extension_approx_nash_expected_payoff_nonneg {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (u : Fin n → ((i : Fin n) → A i) → ℝ)
    (hu : ∀ i a, 0 ≤ u i a ∧ u i a ≤ 1)
    (i : Fin n) (x : (j : Fin n) → stdSimplex ℝ (A j)) :
    0 ≤ normal_form_expected_payoff u i x := by
  unfold normal_form_expected_payoff
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (one_player_extension_approx_nash_prod_nonneg x a) (hu i a).1

lemma one_player_extension_approx_nash_prod_snoc_apply {r : ℕ} {A : Fin (r + 1) → Type} [∀ i, Fintype (A i)]
    (x : (j : Fin r) → stdSimplex ℝ (A j.castSucc))
    (y : stdSimplex ℝ (A (Fin.last r))) (a : (j : Fin (r + 1)) → A j) :
    (∏ j : Fin (r + 1), ((Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x y j : stdSimplex ℝ (A j)).val (a j))) =
    (∏ j : Fin r, (x j).val (a j.castSucc)) * y.val (a (Fin.last r)) := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma one_player_extension_approx_nash_expected_payoff_mix_last {r : ℕ} {A : Fin (r + 1) → Type} [∀ i, Fintype (A i)]
    (u : Fin (r + 1) → ((i : Fin (r + 1)) → A i) → ℝ)
    (x : (j : Fin r) → stdSimplex ℝ (A j.castSucc))
    (y1 y2 : stdSimplex ℝ (A (Fin.last r)))
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (i : Fin (r + 1)) :
    normal_form_expected_payoff u i (Fin.snoc x (stdSimplex.mix θ hθ0 hθ1 y1 y2)) =
    θ * normal_form_expected_payoff u i (Fin.snoc x y1) +
    (1 - θ) * normal_form_expected_payoff u i (Fin.snoc x y2) := by
  unfold normal_form_expected_payoff
  simp_rw [one_player_extension_approx_nash_prod_snoc_apply]
  simp only [stdSimplex.mix_apply]
  have h (a : (j : Fin (r + 1)) → A j) :
    ((∏ j : Fin r, (x j).val (a j.castSucc)) * (θ * y1.val (a (Fin.last r)) + (1 - θ) * y2.val (a (Fin.last r)))) * u i a =
    θ * (((∏ j : Fin r, (x j).val (a j.castSucc)) * y1.val (a (Fin.last r))) * u i a) +
    (1 - θ) * (((∏ j : Fin r, (x j).val (a j.castSucc)) * y2.val (a (Fin.last r))) * u i a) := by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma one_player_extension_approx_nash_expected_payoff_snoc_pure_last {r : ℕ} {A : Fin (r + 1) → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (u : Fin (r + 1) → ((i : Fin (r + 1)) → A i) → ℝ)
    (x : (j : Fin r) → stdSimplex ℝ (A j.castSucc))
    (s : A (Fin.last r)) (k : Fin r) :
    normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure s)) =
    normal_form_expected_payoff (normal_form_subgame_last u s) k x := by
  unfold normal_form_expected_payoff normal_form_subgame_last
  have h_equiv := (Equiv.sum_comp (Fin.snocEquiv A) (fun a =>
    (∏ j : Fin (r + 1), ((Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x (stdSimplex.pure s) j : stdSimplex ℝ (A j)).val (a j))) * u k.castSucc a)).symm
  rw [h_equiv]
  simp_rw [Fintype.sum_prod_type]
  have h_eq (a_last : A (Fin.last r)) (a_init : (j : Fin r) → A j.castSucc) :
    Fin.snocEquiv A (a_last, a_init) = Fin.snoc a_init a_last := rfl
  simp_rw [h_eq]
  have h_prod (a_last : A (Fin.last r)) (a_init : (j : Fin r) → A j.castSucc) :
    (∏ j : Fin (r + 1), ((Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x (stdSimplex.pure s) j : stdSimplex ℝ (A j)).val (Fin.snoc a_init a_last j))) =
    (∏ j : Fin r, (x j).val (a_init j)) * (stdSimplex.pure s : stdSimplex ℝ (A (Fin.last r))).val a_last := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [h_prod, stdSimplex.pure_apply]
  rw [Finset.sum_comm]
  have h_inner (a_init : (j : Fin r) → A j.castSucc) :
    (∑ a_last : A (Fin.last r), ((∏ j : Fin r, (x j).val (a_init j)) * (if a_last = s then (1 : ℝ) else 0)) * u k.castSucc (Fin.snoc a_init a_last)) =
    (∏ j : Fin r, (x j).val (a_init j)) * u k.castSucc (Fin.snoc a_init s) := by
    have h_split (a_last : A (Fin.last r)) :
      ((∏ j : Fin r, (x j).val (a_init j)) * (if a_last = s then (1 : ℝ) else 0)) * u k.castSucc (Fin.snoc a_init a_last) =
      if a_last = s then (∏ j : Fin r, (x j).val (a_init j)) * u k.castSucc (Fin.snoc a_init s) else 0 := by
      split_ifs with h
      · subst h; ring
      · ring
    simp_rw [h_split]
    simp
  simp_rw [h_inner]

/-- One-player extension: extending an α-approximate equilibrium of a restricted subgame yields a 1/(2-α)-approximate equilibrium. -/
theorem one_player_extension_approx_nash {r : ℕ} {A : Fin (r + 1) → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (u : Fin (r + 1) → ((i : Fin (r + 1)) → A i) → ℝ)
    (hu : ∀ i a, 0 ≤ u i a ∧ u i a ≤ 1)
    (s : A (Fin.last r))
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x : (j : Fin r) → stdSimplex ℝ (A j.castSucc))
    (hx : is_approx_nash_equilibrium (normal_form_subgame_last u s) α x)
    (b : A (Fin.last r))
    (hb : is_pure_best_response_last u x b) :
    let θ : ℝ := 1 / (2 - α)
    let y : stdSimplex ℝ (A (Fin.last r)) :=
      stdSimplex.mix θ (div_nonneg zero_le_one (by linarith))
        ((div_le_iff₀ (by linarith : 0 < 2 - α)).mpr (by linarith))
        (stdSimplex.pure s) (stdSimplex.pure b)
    is_approx_nash_equilibrium u θ (Fin.snoc x y) := by
  intro θ y
  have hθ0 : 0 ≤ θ := div_nonneg zero_le_one (by linarith)
  have hθ1 : θ ≤ 1 := (div_le_iff₀ (by linarith : 0 < 2 - α)).mpr (by linarith)
  have h2α : 2 - α ≠ 0 := by linarith
  have h_theta_id : θ * α + (1 - θ) = θ := one_player_extension_theta_identity α h2α
  intro i
  refine Fin.lastCases ?_ ?_ i
  · intro a
    have hup : Function.update (Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x y) (Fin.last r) (stdSimplex.pure a) =
        Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x (stdSimplex.pure a) :=
      Fin.update_snoc_last (α := fun i => stdSimplex ℝ (A i)) y x (stdSimplex.pure a)
    rw [hup]
    have hmix := one_player_extension_approx_nash_expected_payoff_mix_last u x (stdSimplex.pure s) (stdSimplex.pure b) θ hθ0 hθ1 (Fin.last r)
    change normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure a)) -
      normal_form_expected_payoff u (Fin.last r) (Fin.snoc x y) ≤ θ
    rw [hmix]
    have _hba := hb a
    have _hub := one_player_extension_approx_nash_expected_payoff_le_one u hu (Fin.last r) (Fin.snoc x (stdSimplex.pure b))
    have _hus := one_player_extension_approx_nash_expected_payoff_nonneg u hu (Fin.last r) (Fin.snoc x (stdSimplex.pure s))
    calc normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure a)) -
        (θ * normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure s)) +
          (1 - θ) * normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure b)))
      _ ≤ normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure b)) -
        (θ * normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure s)) +
          (1 - θ) * normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure b))) := by linarith
      _ = θ * (normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure b)) -
          normal_form_expected_payoff u (Fin.last r) (Fin.snoc x (stdSimplex.pure s))) := by ring
      _ ≤ θ * 1 := by nlinarith
      _ = θ := mul_one θ
  · intro k a
    have hup : Function.update (Fin.snoc (α := fun i => stdSimplex ℝ (A i)) x y) k.castSucc (stdSimplex.pure a) =
        Fin.snoc (α := fun i => stdSimplex ℝ (A i)) (Function.update x k (stdSimplex.pure a)) y :=
      (Fin.snoc_update (α := fun i => stdSimplex ℝ (A i)) y x k (stdSimplex.pure a)).symm
    rw [hup]
    let x' := Function.update x k (stdSimplex.pure a)
    have hmix' := one_player_extension_approx_nash_expected_payoff_mix_last u x' (stdSimplex.pure s) (stdSimplex.pure b) θ hθ0 hθ1 k.castSucc
    have hmix := one_player_extension_approx_nash_expected_payoff_mix_last u x (stdSimplex.pure s) (stdSimplex.pure b) θ hθ0 hθ1 k.castSucc
    change normal_form_expected_payoff u k.castSucc (Fin.snoc x' y) -
      normal_form_expected_payoff u k.castSucc (Fin.snoc x y) ≤ θ
    rw [hmix', hmix]
    have hxs' := one_player_extension_approx_nash_expected_payoff_snoc_pure_last u x' s k
    have hxs := one_player_extension_approx_nash_expected_payoff_snoc_pure_last u x s k
    have _hnash := hx k a
    have _hub' := one_player_extension_approx_nash_expected_payoff_le_one u hu k.castSucc (Fin.snoc x' (stdSimplex.pure b))
    have _hub := one_player_extension_approx_nash_expected_payoff_nonneg u hu k.castSucc (Fin.snoc x (stdSimplex.pure b))
    calc (θ * normal_form_expected_payoff u k.castSucc (Fin.snoc x' (stdSimplex.pure s)) +
          (1 - θ) * normal_form_expected_payoff u k.castSucc (Fin.snoc x' (stdSimplex.pure b))) -
        (θ * normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure s)) +
          (1 - θ) * normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure b)))
      _ = θ * (normal_form_expected_payoff u k.castSucc (Fin.snoc x' (stdSimplex.pure s)) -
          normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure s))) +
        (1 - θ) * (normal_form_expected_payoff u k.castSucc (Fin.snoc x' (stdSimplex.pure b)) -
          normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure b))) := by ring
      _ = θ * (normal_form_expected_payoff (normal_form_subgame_last u s) k x' -
          normal_form_expected_payoff (normal_form_subgame_last u s) k x) +
        (1 - θ) * (normal_form_expected_payoff u k.castSucc (Fin.snoc x' (stdSimplex.pure b)) -
          normal_form_expected_payoff u k.castSucc (Fin.snoc x (stdSimplex.pure b))) := by rw [hxs', hxs]
      _ ≤ θ * α + (1 - θ) * 1 := by nlinarith
      _ = θ := by linarith [h_theta_id]
