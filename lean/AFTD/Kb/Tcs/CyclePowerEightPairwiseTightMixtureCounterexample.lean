import AFTD.Prelude

/-!
# cycle_power_eight_pairwise_tight_mixture_counterexample

Topic: combinatorics   Node: 11eb51e5eac8

Provenance: helper lemma. Explicit period-three countermodel to a pairwise-consistent fractional relaxation in RT-1, related to arXiv:2610.15635; experiments 27098, 27119 and 27124.

For the displayed period-three family of three equally weighted Boolean classes per phase, every class has the required endpoints, parent implications and dyadic weight equality. The averaged exact ownership, nonmiddle coverage and active count constraints hold with zero defects, and each individual phase has at most one owner. For each pair of phases the displayed scenario map is a permutation and no coupled pair simultaneously owns the same dyadic constraint. Nevertheless the two corrected counts have numerators five and six. This is a counterexample to the specified averaged and pairwise-consistent relaxation, not to the pointwise Boolean model.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def rt1_mixture_classes865 : Fin 3 → Fin 3 → Fin 8 → Bool := ![![![true, false, false, false, false, false, true, true], ![true, true, false, false, false, false, false, true], ![true, true, true, false, true, true, true, true]], ![![true, false, false, false, false, false, false, true], ![true, true, false, false, false, false, false, true], ![true, true, true, false, true, true, true, true]], ![![true, false, false, false, false, false, false, true], ![true, false, false, false, false, false, false, true], ![true, true, true, false, true, true, true, true]]]
def rt1_mixture_parent865 : Fin 8 → Fin 8 := ![0,7,6,7,0,1,0,7]
def rt1_mixture_bit865 (p s : Fin 3) (a : ℕ) : Bool :=
  rt1_mixture_classes865 p s ⟨a % 8, Nat.mod_lt _ (by decide)⟩
def rt1_mixture_x865 (p : Fin 3) (a : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 3)).sum (fun s => (rt1_mixture_bit865 p s a).toNat)
def rt1_mixture_q865 (p : Fin 3) (a b : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 3)).sum (fun s => (rt1_mixture_bit865 p s a && rt1_mixture_bit865 p s b).toNat)
def rt1_mixture_at865 (v : Fin 3) (a : ℕ) : Fin 3 := v - ⟨a % 3, Nat.mod_lt _ (by decide)⟩
def rt1_mixture_owner865 (v j p s : Fin 3) : ℕ :=
  (Finset.range (2^j.val)).sum (fun a =>
    if rt1_mixture_at865 v a = p then
      (rt1_mixture_bit865 p s a && rt1_mixture_bit865 p s (a+8-2^j.val)).toNat
    else 0)
def rt1_mixture_perm865 (p q s : Fin 3) : Fin 3 :=
  if p = 0 ∧ q = 2 then (![0,2,1] : Fin 3 → Fin 3) s
  else (![2,0,1] : Fin 3 → Fin 3) s

/-- An explicit mixture of genuine tight Boolean classes meets all model equations
in average and admits pairwise owner-consistent couplings, while the corrected counts differ.
It does not satisfy the pointwise Boolean model. -/

theorem cycle_power_eight_pairwise_tight_mixture_counterexample :
  (∀ p s : Fin 3, rt1_mixture_bit865 p s 0 = true ∧ rt1_mixture_bit865 p s 7 = true) ∧
  (∀ p s : Fin 3, ∀ a : Fin 8, 0 < a.val → a.val < 7 →
    rt1_mixture_classes865 p s a = true → rt1_mixture_classes865 p s (rt1_mixture_parent865 a) = true) ∧
  (∀ p s : Fin 3,
    2 * (rt1_mixture_bit865 p s 0 && rt1_mixture_bit865 p s 7).toNat +
    (Finset.range 2).sum (fun a => (rt1_mixture_bit865 p s a && rt1_mixture_bit865 p s (a+6)).toNat) +
    (Finset.range 4).sum (fun a => (rt1_mixture_bit865 p s a && rt1_mixture_bit865 p s (a+4)).toNat) =
    (Finset.range 8).sum (fun a => (rt1_mixture_bit865 p s a).toNat)) ∧
  (∀ v : Fin 3, rt1_mixture_q865 v 0 7 = 3) ∧
  (∀ v : Fin 3, (Finset.range 2).sum (fun a => rt1_mixture_q865 (rt1_mixture_at865 v a) a (a+6)) = 3) ∧
  (∀ v : Fin 3, (Finset.range 4).sum (fun a => rt1_mixture_q865 (rt1_mixture_at865 v a) a (a+4)) = 3) ∧
  (∀ v : Fin 3, ∀ d : Fin 8, 1 ≤ d.val → d.val ≠ 4 →
    3 ≤ (Finset.range (8-d.val)).sum (fun a => rt1_mixture_q865 (rt1_mixture_at865 v a) a (a+d.val))) ∧
  (∀ v : Fin 3, (Finset.range 8).sum (fun a => rt1_mixture_x865 (rt1_mixture_at865 v a) a) = 12) ∧
  (∀ v j p s : Fin 3, rt1_mixture_owner865 v j p s ≤ 1) ∧
  (∀ p q : Fin 3, p < q →
    rt1_mixture_perm865 p q 0 ≠ rt1_mixture_perm865 p q 1 ∧
    rt1_mixture_perm865 p q 0 ≠ rt1_mixture_perm865 p q 2 ∧
    rt1_mixture_perm865 p q 1 ≠ rt1_mixture_perm865 p q 2) ∧
  (∀ p q : Fin 3, p < q → ∀ v j s : Fin 3,
    rt1_mixture_owner865 v j p s *
      rt1_mixture_owner865 v j q (rt1_mixture_perm865 p q s) = 0) ∧
  ((Finset.range 4).sum (fun a => rt1_mixture_x865 (rt1_mixture_at865 0 a) a) = 5) ∧
  ((Finset.range 4).sum (fun a => rt1_mixture_x865 (rt1_mixture_at865 1 a) a) = 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
