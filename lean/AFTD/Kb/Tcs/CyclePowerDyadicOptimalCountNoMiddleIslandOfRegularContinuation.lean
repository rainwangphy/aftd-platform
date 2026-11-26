import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicOptimalCountNoMiddleIslandSmall
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_optimal_count_no_middle_island_of_regular_continuation

Topic: combinatorics   Node: 91820f2327e5

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Reduces the stated cycle_power_dyadic_optimal_count_no_middle_island (j ≥ 1) to cycle_power_dyadic_middle_island_regular_neighbourhood and the two continuation statements, which are not proved here.

Conditional proof of the island exclusion for every exponent j+3 ≥ 4. Call a class regular of the first kind if it contains offset 1 and its offsets come in consecutive pairs (2i, 2i+1 both in or both out), and regular of the second kind if it consists of its two endpoints only. Hypotheses, for class models as below: (hIR) without any count, an island class rooted at p forces every class rooted within 7·2^j of p to be regular, of the first kind at even distance from p and of the second kind at odd distance; (hCTr), (hCTl) with exactly t+2 active classes per vertex at exponent t+1 ≥ 4, if the classes on 3·2^t consecutive roots ending (resp. starting) at p0 are regular with the kinds alternating and p0 of the first kind, then the next two classes to the right (resp. left) are regular, of the second and of the first kind. Conclusion: for j ≥ 1, in a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent j+3 with exactly j+4 active classes at every vertex, no class is the island [0, g) ∪ [3g, 5g) ∪ [7g, D), where D = 2^(j+3), g = 2^j.
-/

theorem cycle_power_dyadic_optimal_count_no_middle_island_of_regular_continuation
    (hIR : ∀ j : ℕ, 1 ≤ j → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
        (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat)) →
      (∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      ∀ p : ℤ, (∀ b < 2^(j+3), x p b =
        (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b))) →
      ∀ r : ℤ, p - 7*2^j ≤ r → r ≤ p + 7*2^j →
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+2), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+3) - 1 → x r a = false))
    (hCTr : ∀ t : ℕ, 3 ≤ t → ∀ (x : ℤ → ℕ → Bool),
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
    (hCTl : ∀ t : ℕ, 3 ≤ t → ∀ (x : ℤ → ℕ → Bool),
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
      (∀ r : ℤ, p0 ≤ r → r ≤ p0 + 3*2^t →
        ((r - p0) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
        ((r - p0) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) →
      (∀ a, 0 < a → a < 2^(t+1) - 1 → x (p0-1) a = false) ∧
      (x (p0-2) 1 = true ∧ ∀ i < 2^t, x (p0-2) (2*i) = x (p0-2) (2*i+1)))
    (j : ℕ) (hj : 1 ≤ j) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
      (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(j+3))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (j+3)+1) :
    ∀ p : ℤ, ¬ ∀ b < 2^(j+3), x p b =
      (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b)) := by
  induction j, hj using Nat.le_induction generalizing x with
  | base =>
    exact cycle_power_dyadic_optimal_count_no_middle_island_small 1 le_rfl (by norm_num) x
      htight hexact hcover hcount
  | succ j hj ih =>
    intro p hI
    obtain ⟨G, hG⟩ : ∃ G : ℕ, G = 2^j := ⟨_, rfl⟩
    have hGpos : 0 < G := by rw [hG]; positivity
    have e1 : (2:ℕ)^(j+1) = 2*G := by rw [hG, pow_succ]; ring
    have e3 : (2:ℕ)^(j+3) = 8*G := by rw [hG, pow_succ, pow_succ, pow_succ]; ring
    have e4 : (2:ℕ)^(j+1+3) = 16*G := by rw [hG, pow_succ, pow_succ, pow_succ, pow_succ]; ring
    have e4' : (2:ℕ)^(j+3+1) = 16*G := e4
    have e1z : ((2:ℤ))^(j+1) = 2*(G:ℤ) := by exact_mod_cast e1
    have e3z : ((2:ℤ))^(j+3) = 8*(G:ℤ) := by exact_mod_cast e3
    have hGz : (0:ℤ) < (G:ℤ) := by exact_mod_cast hGpos
    have hreg0 := hIR (j+1) (by omega) x htight hexact hcover p hI
    -- regular structure, stated with G
    have hR0 : ∀ r : ℤ, p - 14*(G:ℤ) ≤ r → r ≤ p + 14*(G:ℤ) →
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+3), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+1+3) - 1 → x r a = false) := by
      intro r h1 h2
      exact hreg0 r (by rw [e1z]; omega) (by rw [e1z]; omega)
    have hright : ∀ n : ℕ, ∀ r : ℤ, p - 14*(G:ℤ) ≤ r → r ≤ p + 14*(G:ℤ) + 2*(n:ℤ) →
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+3), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+1+3) - 1 → x r a = false) := by
      intro n
      induction n with
      | zero => intro r h1 h2; exact hR0 r h1 (by simpa using h2)
      | succ n ihn =>
        intro r h1 h2
        by_cases hle : r ≤ p + 14*(G:ℤ) + 2*(n:ℤ)
        · exact ihn r h1 hle
        · have hstep := hCTr (j+3) (by omega) x htight hexact hcover hcount (p + 14*(G:ℤ) + 2*(n:ℤ))
            (by
              intro r' hr1 hr2
              have hw := ihn r' (by rw [e3z] at hr1; omega) hr2
              refine ⟨fun hpar => hw.1 (by omega), fun hpar => hw.2 (by omega)⟩)
          push_cast at h2
          rcases (show r = p + 14*(G:ℤ) + 2*(n:ℤ) + 1 ∨ r = p + 14*(G:ℤ) + 2*(n:ℤ) + 2 by omega) with rfl | rfl
          · exact ⟨fun hpar => by omega, fun _ => hstep.1⟩
          · exact ⟨fun _ => hstep.2, fun hpar => by omega⟩
    have hleft : ∀ n : ℕ, ∀ r : ℤ, p - 14*(G:ℤ) - 2*(n:ℤ) ≤ r → r ≤ p + 14*(G:ℤ) →
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+3), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+1+3) - 1 → x r a = false) := by
      intro n
      induction n with
      | zero => intro r h1 h2; exact hR0 r (by simpa using h1) h2
      | succ n ihn =>
        intro r h1 h2
        by_cases hle : p - 14*(G:ℤ) - 2*(n:ℤ) ≤ r
        · exact ihn r hle h2
        · have hstep := hCTl (j+3) (by omega) x htight hexact hcover hcount (p - 14*(G:ℤ) - 2*(n:ℤ))
            (by
              intro r' hr1 hr2
              have hw := ihn r' hr1 (by rw [e3z] at hr2; omega)
              refine ⟨fun hpar => hw.1 (by omega), fun hpar => hw.2 (by omega)⟩)
          push_cast at h1
          rcases (show r = p - 14*(G:ℤ) - 2*(n:ℤ) - 1 ∨ r = p - 14*(G:ℤ) - 2*(n:ℤ) - 2 by omega) with rfl | rfl
          · exact ⟨fun hpar => by omega, fun _ => hstep.1⟩
          · exact ⟨fun _ => hstep.2, fun hpar => by omega⟩
    have hall : ∀ r : ℤ,
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+3), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+1+3) - 1 → x r a = false) := by
      intro r
      rcases le_total r (p + 14*(G:ℤ)) with h | h
      · refine hleft (p - r).toNat r ?_ h
        have := Int.toNat_of_nonneg (show (0:ℤ) ≤ (p - r).toNat by positivity)
        rcases le_total 0 (p - r) with h0 | h0
        · rw [Int.toNat_of_nonneg h0]; omega
        · rw [Int.toNat_of_nonpos h0]; omega
      · refine hright (r - p).toNat r (by omega) ?_
        rw [Int.toNat_of_nonneg (by omega)]; omega
    have hone : (1:ℕ) < 2^(j+1+3) - 1 := by rw [e4]; omega
    have halt : ∀ q : ℤ, x (q+1) 1 = !x q 1 := by
      intro q
      rcases Int.emod_two_eq_zero_or_one (q - p) with h | h
      · rw [((hall q).1 h).1, (hall (q+1)).2 (by omega) 1 (by norm_num) hone]; rfl
      · rw [(hall q).2 h 1 (by norm_num) hone, ((hall (q+1)).1 (by omega)).1]; rfl
    have hend : ∀ q : ℤ, x q 1 = false → ∀ a, 0 < a → a < 2^(j+3+1) - 1 → x q a = false := by
      intro q hq a ha1 ha2
      rcases Int.emod_two_eq_zero_or_one (q - p) with h | h
      · rw [((hall q).1 h).1] at hq; exact absurd hq (by decide)
      · exact (hall q).2 h a ha1 ha2
    have hs : x p 1 = true := ((hall p).1 (by simp)).1
    obtain ⟨yt, yex, ycv, ycn⟩ := cycle_power_dyadic_alternating_half_model (j+3) (by omega) x
      htight hexact hcover hcount halt hend p hs 0 (by norm_num)
    refine ih (fun q b => x (2*q+p) (2*b+0)) yt yex ycv ycn 0 ?_
    intro b hb
    show x (2*0+p) (2*b+0) = _
    rw [show (2*0+p : ℤ) = p by ring, Nat.add_zero, hI (2*b) (by rw [e4]; rw [e3] at hb; omega)]
    rw [e1, ← hG]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
