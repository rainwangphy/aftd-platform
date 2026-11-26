import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect
import AFTD.Kb.Tcs.CyclePowerRootedReflectExact
import AFTD.Kb.Tcs.CyclePowerRootedReflectCover
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightReflect
import AFTD.Kb.Tcs.CyclePowerReflectCountDefect
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_regular_continuation_left_of_right

Topic: combinatorics   Node: cf745f3314b1

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Removes the leftward continuation hypothesis: cycle_power_dyadic_regular_continuation_left follows from cycle_power_dyadic_regular_continuation_right.

The leftward continuation follows from the rightward one, exponent by exponent. Call a class regular of the first kind if it contains offset 1 and its offsets come in consecutive pairs (2i, 2i+1 both in or both out), and regular of the second kind if it consists of its two endpoints only. Fix t and suppose that in every tight, exactly dyadically covered, fully covered integer Boolean class model at exponent t+1 with exactly t+2 active classes per vertex, whenever the classes rooted at p0 - 3·2^t, ..., p0 are regular with kinds alternating and p0 of the first kind, the class rooted at p0+1 is of the second kind and the class rooted at p0+2 of the first kind. Then in every such model, whenever the classes rooted at p0, ..., p0 + 3·2^t are regular with kinds alternating and p0 of the first kind, the class rooted at p0-1 is of the second kind and the class rooted at p0-2 of the first kind.
-/

theorem cycle_power_dyadic_regular_continuation_left_of_right (t : ℕ)
    (hCTr : ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
        (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat)) →
      (∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (t+1)+1) →
      ∀ p0 : ℤ,
      (∀ r : ℤ, p0 - 3*2^t ≤ r → r ≤ p0 →
        ((p0 - r) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
        ((p0 - r) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) →
      (∀ a, 0 < a → a < 2^(t+1) - 1 → x (p0+1) a = false) ∧
      (x (p0+2) 1 = true ∧ ∀ i < 2^t, x (p0+2) (2*i) = x (p0+2) (2*i+1)))
    (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (p0 : ℤ)
    (hreg : ∀ r : ℤ, p0 ≤ r → r ≤ p0 + 3*2^t →
      ((r - p0) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
      ((r - p0) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) :
    (∀ a, 0 < a → a < 2^(t+1) - 1 → x (p0-1) a = false) ∧
    (x (p0-2) 1 = true ∧ ∀ i < 2^t, x (p0-2) (2*i) = x (p0-2) (2*i+1)) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2^t := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hD : (2:ℕ)^(t+1) = 2*T := by rw [hT, pow_succ]; ring
  have hDpos : 0 < (2:ℕ)^(t+1) := by positivity
  have hTz : ((2:ℤ))^t = (T:ℤ) := by rw [hT]; push_cast; rfl
  have hcast : (((2^(t+1) - 1 : ℕ)) : ℤ) = 2*(T:ℤ) - 1 := by
    rw [hD]; omega
  have hx : ∀ (q q' : ℤ) (a a' : ℕ), q = q' → a = a' → x q a = x q' a' := by
    intro q q' a a' h1 h2; rw [h1, h2]
  have hends : ∀ v : ℤ, x v 0 = true ∧ x v (2^(t+1) - 1) = true := by
    intro v
    have h := hexact 0 (by omega) v
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
      Nat.zero_add] at h
    revert h
    generalize x v 0 = u
    generalize x v (2^(t+1) - 1) = w
    cases u <;> cases w <;> simp
  let y : ℤ → ℕ → Bool := cycle_power_rooted_reflect (2^(t+1)) x
  have yd : ∀ (q : ℤ) (a : ℕ), y q a = x (-q - ((2^(t+1) - 1 : ℕ) : ℤ)) (2^(t+1) - 1 - a) :=
    fun _ _ => rfl
  have ytight : ∀ p, cycle_power_dyadic_class_weight (t+1) (y p) =
      (Finset.range (2^(t+1))).sum (fun a => (y p a).toNat) := by
    intro p
    change cycle_power_dyadic_class_weight (t+1)
      (fun a => x (-p - ((2^(t+1) - 1 : ℕ) : ℤ)) (2^(t+1) - 1 - a)) = _
    rw [cycle_power_dyadic_class_weight_reflect, htight]
    exact (Finset.sum_range_reflect
      (fun a => (x (-p - ((2^(t+1) - 1 : ℕ) : ℤ)) a).toNat) (2^(t+1))).symm
  have yexact : ∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1 := by
    intro i hi
    exact cycle_power_rooted_reflect_exact (2^(t+1)) (2^i) (by positivity)
      (Nat.pow_le_pow_right (by norm_num) (by omega)) x (hexact i hi)
  have ycover := cycle_power_rooted_reflect_cover (2^(t+1)) hDpos x hcover
  have ycount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (y (v-(a : ℤ)) a).toNat) = (t+1)+1 := by
    intro v
    have h := cycle_power_reflect_count_defect (2^(t+1)) hDpos x (fun _ => false) ((t+1)+1)
      (by intro w; simpa using hcount w) v
    simpa using h
  have hmain := hCTr y ytight yexact ycover ycount (-p0 - ((2^(t+1) - 1 : ℕ) : ℤ)) (by
    intro r' hr1 hr2
    rw [hcast, hTz] at hr1
    rw [hcast] at hr2
    have hw := hreg (-r' - ((2^(t+1) - 1 : ℕ) : ℤ)) (by rw [hcast]; omega) (by rw [hcast, hTz]; omega)
    refine ⟨fun hpar => ?_, fun hpar => ?_⟩
    · obtain ⟨_, hp⟩ := hw.1 (by rw [hcast] at hpar ⊢; omega)
      refine ⟨?_, fun i hi => ?_⟩
      · rw [yd]
        have h1 := hp (T - 1) (by rw [← hT]; omega)
        have h2 := (hends (-r' - ((2^(t+1) - 1 : ℕ) : ℤ))).2
        rw [hx _ _ (2^(t+1) - 1 - 1) (2*(T-1)) rfl (by rw [hD]; omega), h1,
          hx _ _ (2*(T-1)+1) (2^(t+1) - 1) rfl (by rw [hD]; omega), h2]
      · rw [yd, yd]
        rw [← hT] at hi
        have h1 := hp (T - 1 - i) (by rw [← hT]; omega)
        rw [hx _ _ (2^(t+1) - 1 - 2*i) (2*(T-1-i)+1) rfl (by rw [hD]; omega), ← h1]
        exact hx _ _ _ _ rfl (by rw [hD]; omega)
    · intro a ha1 ha2
      rw [yd]
      exact hw.2 (by rw [hcast] at hpar ⊢; omega) _ (by omega) (by omega))
  have hq1 : -(-p0 - ((2^(t+1) - 1 : ℕ) : ℤ) + 1) - ((2^(t+1) - 1 : ℕ) : ℤ) = p0 - 1 := by ring
  have hq2 : -(-p0 - ((2^(t+1) - 1 : ℕ) : ℤ) + 2) - ((2^(t+1) - 1 : ℕ) : ℤ) = p0 - 2 := by ring
  obtain ⟨hA, _, hC⟩ := hmain
  have hpair : ∀ i < 2^t, x (p0-2) (2*i) = x (p0-2) (2*i+1) := by
    intro i hi
    rw [← hT] at hi
    have h := hC (T - 1 - i) (by rw [← hT]; omega)
    rw [yd, yd, hq2] at h
    rw [hx (p0-2) (p0-2) (2*i) (2^(t+1) - 1 - (2*(T-1-i)+1)) rfl (by rw [hD]; omega), ← h]
    exact hx _ _ _ _ rfl (by rw [hD]; omega)
  refine ⟨fun a ha1 ha2 => ?_, ?_, hpair⟩
  · have h := hA (2^(t+1) - 1 - a) (by omega) (by omega)
    rw [yd, hq1] at h
    rw [← h]
    exact hx _ _ _ _ rfl (by omega)
  · have h := hpair 0 (by positivity)
    simp only [Nat.mul_zero, Nat.zero_add] at h
    rw [← h]
    exact (hends (p0-2)).1
