import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.Tcs.ForestGreedyLawEnveloped
import AFTD.Kb.Tcs.ForestCarpoolFibonacciEnvelopeDecay
import AFTD.Kb.Tcs.ForestGreedyThresholdEventCount
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# forest_greedy_envelope_preserved_by_independent_merge

Topic: online_algorithms   Node: de50b1979c4a

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

Independent symmetric finite uniform discrepancy laws of fixed parity that satisfy the envelope still satisfy it after one greedy step using an independent fair tie coin.
-/

namespace ForestGreedyMerge

theorem card_comp_equiv {γ : Type} [Fintype γ] (Φ : γ ≃ γ) (f : γ → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun p => f (Φ p))).card = (Finset.univ.filter f).card := by
  refine Finset.card_nbij' Φ Φ.symm ?_ ?_ (fun p _ => Φ.symm_apply_apply p)
    (fun p _ => Φ.apply_symm_apply p)
  · intro p hp; simpa using hp
  · intro p hp; simpa using hp

theorem exists_neg_equiv (α : Type) [Fintype α] (X : α → ℤ)
    (h : ∀ z : ℤ, (Finset.univ.filter (fun a => X a = z)).card =
      (Finset.univ.filter (fun a => X a = -z)).card) :
    ∃ σ : α ≃ α, ∀ a, X (σ a) = - X a := by
  classical
  have e : ∀ c : ℤ, {a // X a = c} ≃ {b // (fun b => -X b) b = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype, h c]
      congr 1; ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  refine ⟨(Equiv.ofFiberEquiv e).symm, fun a => ?_⟩
  have := Equiv.ofFiberEquiv_map e ((Equiv.ofFiberEquiv e).symm a)
  simp only [Equiv.apply_symm_apply] at this
  linarith

theorem step_neg (x y : ℤ) (c : Bool) :
    forest_greedy_signed_step (-x) (-y) (!c) = - forest_greedy_signed_step x y c := by
  unfold forest_greedy_signed_step
  cases c <;> split_ifs <;> first | omega | (exfalso; simp_all)

theorem mid_hi_card (α : Type) [Fintype α] (X : α → ℤ) (j : ℤ) :
    (Finset.univ.filter (fun a => j ≤ X a ∧ X a ≤ j + 1)).card +
      (Finset.univ.filter (fun a => j + 2 ≤ X a)).card =
    (Finset.univ.filter (fun a => j ≤ X a)).card := by
  classical
  have := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun a => j ≤ X a)) (fun a => X a ≤ j + 1)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  have h4 : (Finset.univ.filter (fun a => j ≤ X a ∧ X a ≤ j + 1)) =
      Finset.univ.filter (fun a => j ≤ X a ∧ X a ≤ j + 1) := rfl
  have h5 : (Finset.univ.filter (fun a => j ≤ X a ∧ ¬ X a ≤ j + 1)) =
      Finset.univ.filter (fun a => j + 2 ≤ X a) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [h5] at this
  exact this

theorem allow_card (β : Type) [Fintype β] (Y : β → ℤ) (j : ℤ) :
    (Finset.univ.filter (fun p : β × Bool =>
        j < Y p.1 ∨ (j = Y p.1 ∧ p.2 = true))).card ≤
      (Finset.univ.filter (fun b => j + 1 ≤ Y b)).card +
      (Finset.univ.filter (fun b => j ≤ Y b)).card := by
  classical
  have hsub : Finset.univ.filter (fun p : β × Bool => j < Y p.1 ∨ (j = Y p.1 ∧ p.2 = true)) ⊆
      ((Finset.univ.filter (fun b => j + 1 ≤ Y b)) ×ˢ (Finset.univ : Finset Bool)) ∪
      ((Finset.univ.filter (fun b => Y b = j)) ×ˢ ({true} : Finset Bool)) := by
    rintro ⟨b, c⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton, and_true]
    rcases hp with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1.symm, h2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    ((Finset.univ.filter (fun b => j + 1 ≤ Y b)) ×ˢ (Finset.univ : Finset Bool))
    ((Finset.univ.filter (fun b => Y b = j)) ×ˢ ({true} : Finset Bool))
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_singleton] at h2
  have h3 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun b => j ≤ Y b)) (fun b => Y b = j)
  rw [Finset.filter_filter, Finset.filter_filter] at h3
  have h4 : (Finset.univ.filter (fun b => j ≤ Y b ∧ Y b = j)) =
      Finset.univ.filter (fun b => Y b = j) := by
    ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have h5 : (Finset.univ.filter (fun b => j ≤ Y b ∧ ¬ Y b = j)) =
      Finset.univ.filter (fun b => j + 1 ≤ Y b) := by
    ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [h4, h5] at h3
  omega

end ForestGreedyMerge

theorem forest_greedy_envelope_preserved_by_independent_merge
    (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (X : α → ℤ) (Y : β → ℤ)
    (hX : forest_greedy_law_enveloped α X)
    (hY : forest_greedy_law_enveloped β Y) :
  forest_greedy_law_enveloped (α × β × Bool)
    (fun p => forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2) := by
  obtain ⟨⟨pX, hpX⟩, hsX, htX⟩ := hX
  obtain ⟨⟨pY, hpY⟩, hsY, htY⟩ := hY
  set Z : α × β × Bool → ℤ := fun p => forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2 with hZ
  obtain ⟨σ, hσ⟩ := ForestGreedyMerge.exists_neg_equiv α X hsX
  obtain ⟨τ, hτ⟩ := ForestGreedyMerge.exists_neg_equiv β Y hsY
  let Φ : α × β × Bool ≃ α × β × Bool := σ.prodCongr (τ.prodCongr Equiv.boolNot)
  have hΦ : ∀ p, Z (Φ p) = - Z p := by
    rintro ⟨a, b, c⟩
    simp only [hZ, Φ, Equiv.prodCongr_apply, Prod.map, hσ, hτ, Equiv.boolNot_apply]
    exact ForestGreedyMerge.step_neg _ _ _
  have hA : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (α × β × Bool) : ℝ) = Fintype.card α * (Fintype.card β * 2) := by
    simp [Fintype.card_prod, Fintype.card_bool]
  refine ⟨⟨(pX + 1) % 2, ?_⟩, ?_, ?_⟩
  · intro p
    have h := hpX p.1
    simp only [hZ, forest_greedy_signed_step]
    split_ifs <;> omega
  · intro z
    rw [← ForestGreedyMerge.card_comp_equiv Φ (fun p => Z p = -z)]
    congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦ]; omega
  · intro k hk
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- k = 1: symmetry
      have hk1' : k = 1 := by omega
      subst hk1'
      simp only [Nat.cast_one]
      have hsym : (Finset.univ.filter (fun p => (1 : ℤ) ≤ Z p)).card =
          (Finset.univ.filter (fun p => Z p ≤ -1)).card := by
        rw [← ForestGreedyMerge.card_comp_equiv Φ (fun p => Z p ≤ -1)]
        congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦ]; omega
      have hdis := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun p => (1 : ℤ) ≤ Z p)
      have hsub : (Finset.univ.filter (fun p => Z p ≤ -1)) ⊆
          Finset.univ.filter (fun p => ¬ (1 : ℤ) ≤ Z p) := by
        intro p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_univ] at hdis
      have hle : 2 * (Finset.univ.filter (fun p => (1 : ℤ) ≤ Z p)).card ≤
          Fintype.card (α × β × Bool) := by omega
      have hpos : (0 : ℝ) < Fintype.card (α × β × Bool) := by
        exact_mod_cast Fintype.card_pos
      have hU : (forest_carpool_tail_envelope 1) = 1 / 2 := by
        simp [forest_carpool_tail_envelope]
      have hle' : (2 : ℝ) * ((Finset.univ.filter (fun p => (1 : ℤ) ≤ Z p)).card : ℝ) ≤
          Fintype.card (α × β × Bool) := by exact_mod_cast hle
      have hmine : ((Finset.univ.filter (fun p => (1 : ℤ) ≤ Z p)).card : ℝ) /
          (Fintype.card (α × β × Bool) : ℝ) ≤ forest_carpool_tail_envelope 1 := by
        rw [div_le_iff₀ hpos, hU]; linarith
      convert hmine using 4
    · -- k ≥ 2
      have hcast : (((k - 1 : ℕ)) : ℤ) = (k : ℤ) - 1 := by omega
      have hev := forest_greedy_threshold_event_count α β X Y (k : ℤ)
      rw [Fintype.card_prod, Fintype.card_bool] at hev
      have hmh := ForestGreedyMerge.mid_hi_card α X ((k : ℤ) - 1)
      rw [show (k : ℤ) - 1 + 1 = k by ring, show (k : ℤ) - 1 + 2 = k + 1 by ring] at hmh
      have hal := ForestGreedyMerge.allow_card β Y ((k : ℤ) - 1)
      rw [show (k : ℤ) - 1 + 1 = k by ring] at hal
      have hylo : (Finset.univ.filter (fun b => (k : ℤ) ≤ Y b)).card ≤
          (Finset.univ.filter (fun b => (k : ℤ) - 1 ≤ Y b)).card := by
        apply Finset.card_le_card
        intro b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hal2 := Finset.card_le_univ (Finset.univ.filter (fun p : β × Bool =>
          (k : ℤ) - 1 < Y p.1 ∨ ((k : ℤ) - 1 = Y p.1 ∧ p.2 = true)))
      rw [Fintype.card_prod, Fintype.card_bool] at hal2
      have eXhi := htX (k + 1) (by omega)
      have eXlo := htX (k - 1) (by omega)
      have eYk := htY k (by omega)
      have eYlo := htY (k - 1) (by omega)
      push_cast at eXhi
      simp only [hcast] at eXlo eYlo
      have hgoal' : ((Finset.univ.filter (fun p : α × β × Bool =>
          (k : ℤ) ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card : ℝ) /
          ((Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * 2)) ≤ forest_carpool_tail_envelope k := by
        generalize (Finset.univ.filter (fun p : α × β × Bool =>
          (k : ℤ) ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card = ev at hev ⊢
        generalize (Finset.univ.filter (fun a => (k : ℤ) + 1 ≤ X a)).card = hi at hev hmh eXhi
        generalize (Finset.univ.filter (fun a => (k : ℤ) - 1 ≤ X a ∧ X a ≤ k)).card = mid at hev hmh
        generalize (Finset.univ.filter (fun a => (k : ℤ) - 1 ≤ X a)).card = lo at hmh eXlo
        generalize (Finset.univ.filter (fun p : β × Bool =>
          (k : ℤ) - 1 < Y p.1 ∨ ((k : ℤ) - 1 = Y p.1 ∧ p.2 = true))).card = al at hev hal hal2
        generalize (Finset.univ.filter (fun b => (k : ℤ) ≤ Y b)).card = yk at hal hylo eYk
        generalize (Finset.univ.filter (fun b => (k : ℤ) - 1 ≤ Y b)).card = ylo at hal hylo eYlo
        generalize (Fintype.card α) = A at hA eXhi eXlo ⊢
        generalize (Fintype.card β) = B at hB eYk eYlo hal2 hev ⊢
        have hev' : (ev : ℝ) ≤ hi * (B * 2) + mid * al := by exact_mod_cast hev
        have hmh' : (mid : ℝ) + hi = lo := by exact_mod_cast hmh
        have hal' : (al : ℝ) ≤ yk + ylo := by exact_mod_cast hal
        have hylo' : (yk : ℝ) ≤ ylo := by exact_mod_cast hylo
        have hal2' : (al : ℝ) ≤ B * 2 := by exact_mod_cast hal2
        have hAr : (0 : ℝ) < A := hA
        have hBr : (0 : ℝ) < B := hB
        set h : ℝ := hi / A with hh
        set m : ℝ := mid / A with hm
        set s : ℝ := al / (2 * B) with hs
        set lq : ℝ := lo / A with hlq
        have hm0 : 0 ≤ m := by positivity
        have hh0 : 0 ≤ h := by positivity
        have hs0 : 0 ≤ s := by positivity
        have hs1 : s ≤ 1 := by
          rw [hs, div_le_one (by positivity)]; linarith
        have hhm : h + m = lq := by
          rw [hh, hm, hlq, ← add_div, add_comm]; congr 1
        have hs2 : 2 * s ≤ yk / B + ylo / B := by
          rw [hs, ← add_div, show 2 * ((al : ℝ) / (2 * B)) = al / B by field_simp]
          exact div_le_div_of_nonneg_right hal' hBr.le
        have hsY : s ≤ ylo / B := by
          have : (yk : ℝ) / B ≤ ylo / B := div_le_div_of_nonneg_right hylo' hBr.le
          linarith
        have hq : (ev : ℝ) / (A * (B * 2)) ≤ h + m * s := by
          rw [div_le_iff₀ (by positivity)]
          have e1 : h * (A * (B * 2)) = hi * (B * 2) := by
            rw [hh]; field_simp
          have e2 : m * s * (A * (B * 2)) = mid * al := by
            rw [hm, hs]; field_simp
          nlinarith [e1, e2]
        have hmain : h + m * s ≤ forest_carpool_tail_envelope (k + 1) * (1 - s) +
            forest_carpool_tail_envelope (k - 1) * s := by
          have hlqU : lq ≤ forest_carpool_tail_envelope (k - 1) := eXlo
          have hhU : h ≤ forest_carpool_tail_envelope (k + 1) := eXhi
          nlinarith [mul_nonneg hm0 hs0, mul_le_mul_of_nonneg_right hhU (by linarith : 0 ≤ 1 - s),
            mul_le_mul_of_nonneg_right hlqU hs0]
        have hU : forest_carpool_tail_envelope (k + 1) * (1 - s) +
            forest_carpool_tail_envelope (k - 1) * s ≤ forest_carpool_tail_envelope k := by
          rcases Nat.lt_or_ge k 4 with hk4 | hk4
          · have u1 : forest_carpool_tail_envelope 1 = 1 / 2 := by
              simp [forest_carpool_tail_envelope]
            have u2 : forest_carpool_tail_envelope 2 = 3 / 8 := by
              simp [forest_carpool_tail_envelope]
            have u3 : forest_carpool_tail_envelope 3 = 1 / 4 := by
              simp [forest_carpool_tail_envelope, Nat.fib_add_two]; norm_num
            have u4 : forest_carpool_tail_envelope 4 = 1 / 8 := by
              simp [forest_carpool_tail_envelope, Nat.fib_add_two]; norm_num
            interval_cases k
            · rw [show (2 : ℕ) + 1 = 3 from rfl, show (2 : ℕ) - 1 = 1 from rfl, u1, u2, u3] at *
              linarith
            · rw [show (3 : ℕ) + 1 = 4 from rfl, show (3 : ℕ) - 1 = 2 from rfl, u2, u3, u4] at *
              linarith
          · have hdec := forest_carpool_fibonacci_envelope_decay k hk4
            have hU0 : 0 ≤ forest_carpool_tail_envelope (k + 1) := by
              unfold forest_carpool_tail_envelope; split_ifs <;> positivity
            have hU1 : 0 ≤ forest_carpool_tail_envelope (k - 1) := by
              unfold forest_carpool_tail_envelope; split_ifs <;> positivity
            nlinarith [mul_le_mul_of_nonneg_left (hsY.trans eYlo) hU1, mul_nonneg hU0 hs0]
        linarith
      rw [hcard] at *
      convert hgoal' using 4
