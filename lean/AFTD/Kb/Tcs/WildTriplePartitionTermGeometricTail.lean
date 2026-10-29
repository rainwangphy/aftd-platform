import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# wild_triple_partition_term_geometric_tail

Topic: graphs   Node: 0d2805849240

Provenance: helper lemma. IN-359 technical helper for the existing permutation resource criterion for OP-306, https://arxiv.org/html/2610.22142v1 Section6. Elementary central-binomial induction and the already proved Vandermonde estimates wtc_choose_cube and wtc_choose_square. No improved wild-number bound or research advance is asserted.

For q>=3 odd and any h>=5 with2*h<=q, the existing canonical triple-partition resource term wtc_term(q,h) is at most 3*h*(27/40)^h. The term is3*h*choose(q,h)*choose(floor(3*q/2), floor(3*h/2))/choose(3*q,3*h)*(21/20)^(3*h). This is a uniform tail estimate for the sufficient resource criterion, not a statement that the full resource sum satisfies its threshold.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem wild_central_binomial_step (h : ℕ) (hh : 1 ≤ h) :
    3 * (2*h).choose h ≤ (2*(h+1)).choose (h+1) := by
  have hs : (2*h+1).choose h = (2*h+1).choose (h+1) :=
    (Nat.choose_symm_half h).symm
  have he := Nat.add_one_mul_choose_eq (2*h) h
  have hn : (2*(h+1)).choose (h+1) = 2 * (2*h+1).choose (h+1) := by
    rw [show 2*(h+1) = (2*h+1)+1 by omega, Nat.choose_succ_succ, hs]
    change (2*h+1).choose (h+1) + (2*h+1).choose (h+1) =
      2 * (2*h+1).choose (h+1)
    ring
  apply Nat.le_of_mul_le_mul_right (c := h+1) (hc := by omega)
  calc
    3 * (2*h).choose h * (h+1) = 3*(h+1)*(2*h).choose h := by ring
    _ ≤ (2*(2*h+1))*(2*h).choose h :=
      Nat.mul_le_mul_right _ (by omega)
    _ = (2 * (2*h+1).choose (h+1))*(h+1) := by nlinarith [he]
    _ = _ := by rw [hn]

theorem wild_central_binomial_ge_three_pow (h : ℕ) (hh : 5 ≤ h) :
    3^h ≤ (2*h).choose h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih =>
    calc
      3^(h+1) = 3*3^h := by rw [pow_succ]; ring
      _ ≤ 3*(2*h).choose h := Nat.mul_le_mul_left _ ih
      _ ≤ _ := wild_central_binomial_step h (by omega)

theorem wild_triple_partition_term_geometric_tail
    (q h : ℕ) (hq : 3 ≤ q) (hodd : q%2 = 1)
    (hh : 5 ≤ h) (hhq : 2*h ≤ q) :
    wtc_term q h ≤ 3*(h : ℝ)*(27/40 : ℝ)^h := by
  let B : ℝ := q.choose h
  let C : ℝ := (3*q).choose (3*h)
  let D : ℝ := (3*q/2).choose (3*h/2)
  have hb : 0 < B := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos (by omega : h ≤ q)
  have hc : 0 < C := by
    dsimp [C]
    exact_mod_cast Nat.choose_pos (by omega : 3*h ≤ 3*q)
  have hd : 0 ≤ D := by positivity
  have hb3 : B^3 ≤ C := by
    dsimp [B,C]
    exact_mod_cast wtc_choose_cube q h
  have hn : 2*(3*q/2)+1 = 3*q := by omega
  have hd2 : D^2 ≤ C := by
    dsimp [D,C]
    exact_mod_cast (hn ▸ wtc_choose_square (3*q/2) (3*h))
  have hlow : (3 : ℝ)^h ≤ B := by
    have hnlow := (wild_central_binomial_ge_three_pow h hh).trans
      (Nat.choose_le_choose h hhq)
    dsimp [B]
    exact_mod_cast hnlow
  have hratio : B*(B*D/C)^2 ≤ 1 := by
    have hmul : B^3*D^2 ≤ C^2 := by
      simpa only [pow_two] using mul_le_mul hb3 hd2 (by positivity : 0 ≤ D^2) hc.le
    have he : B*(B*D/C)^2 = (B^3*D^2)/C^2 := by ring
    rw [he, div_le_one (sq_pos_of_pos hc)]
    exact hmul
  have hratio' : (3 : ℝ)^h*(B*D/C)^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hlow (sq_nonneg _)).trans hratio
  have hpower : ((21/20 : ℝ)^(3*h))^2 ≤
      (3 : ℝ)^h*((27/40 : ℝ)^h)^2 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (21/20)^6)
      (by norm_num : (21/20 : ℝ)^6 ≤ 3*(27/40 : ℝ)^2) h
    have he1 : 3*h*2 = 6*h := by omega
    have he2 : 2*h = h*2 := by omega
    simpa only [mul_pow,← pow_mul,he1,he2] using hp
  have hproduct : (B*D/C)^2*((21/20 : ℝ)^(3*h))^2 ≤ ((27/40 : ℝ)^h)^2 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (3 : ℝ)^h)).mp
    calc
      _ = ((3 : ℝ)^h*(B*D/C)^2)*((21/20 : ℝ)^(3*h))^2 := by ring
      _ ≤ 1*((3 : ℝ)^h*((27/40 : ℝ)^h)^2) :=
        mul_le_mul hratio' hpower (by positivity) (by positivity)
      _ = _ := by ring
  have heq : (wtc_term q h)^2 =
      9*(h : ℝ)^2*((B*D/C)^2*((21/20 : ℝ)^(3*h))^2) := by
    dsimp [wtc_term,B,C,D]
    push_cast
    ring
  have hsquare : (wtc_term q h)^2 ≤ (3*(h : ℝ)*(27/40 : ℝ)^h)^2 := by
    rw [heq]
    calc
      _ ≤ 9*(h : ℝ)^2*((27/40 : ℝ)^h)^2 :=
        mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤ 3*(h : ℝ)*(27/40 : ℝ)^h := by positivity
  have ht : 0 ≤ wtc_term q h := by unfold wtc_term; positivity
  exact (sq_le_sq₀ ht hnonneg).mp hsquare
