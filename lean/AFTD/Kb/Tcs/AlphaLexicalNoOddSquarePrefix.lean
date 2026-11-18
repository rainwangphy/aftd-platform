import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.Tcs.AlphaLexicalLtAppendParity
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# alpha_lexical_no_odd_square_prefix

Topic: combinatorics   Node: 7098eea24172

Provenance: helper lemma. Helper for OP-392, arXiv:2610.24758; the odd-square exclusion is stated as Lemma 2.7 of DOI:10.1006/jcta.2000.3112.

No lexical sequence begins with two copies of the same odd-length sequence.
-/

theorem alpha_nosq_signed_eq_zero_of_le (A : List ℕ) (j : ℕ) (h : A.length ≤ j) :
    alpha_signed_cell A j = 0 := by
  unfold alpha_signed_cell
  rw [List.getD_eq_default _ _ h]; split_ifs <;> simp

theorem alpha_nosq_lt_iff_first_diff (A B : List ℕ) (p : ℕ)
    (heq : ∀ j < p, alpha_signed_cell A j = alpha_signed_cell B j)
    (hne : alpha_signed_cell A p ≠ alpha_signed_cell B p) :
    alpha_lexical_lt A B ↔ alpha_signed_cell A p < alpha_signed_cell B p := by
  constructor
  · rintro ⟨i, _, hpre, hlt⟩
    rcases lt_trichotomy i p with h | h | h
    · exact absurd (heq i h) (ne_of_lt hlt)
    · exact h ▸ hlt
    · exact absurd (hpre p h) hne
  · intro hlt
    refine ⟨p, ?_, heq, hlt⟩
    by_contra hp
    push Not at hp
    apply hne
    rw [alpha_nosq_signed_eq_zero_of_le A p (le_trans (le_max_left _ _) hp),
      alpha_nosq_signed_eq_zero_of_le B p (le_trans (le_max_right _ _) hp)]

theorem alpha_nosq_signed_append_left (u X : List ℕ) (j : ℕ) (hj : j < u.length) :
    alpha_signed_cell (u ++ X) j = alpha_signed_cell u j := by
  unfold alpha_signed_cell
  rw [List.getD_append _ _ _ _ hj]

theorem alpha_nosq_signed_inj (A B : List ℕ) (j : ℕ)
    (h : alpha_signed_cell A j = alpha_signed_cell B j) : A.getD j 0 = B.getD j 0 := by
  unfold alpha_signed_cell at h
  split_ifs at h <;> omega

theorem alpha_nosq_core (u : List ℕ) (hu : ∀ v ∈ u, 0 < v) (hodd : u.length % 2 = 1) :
    ∀ t : List ℕ,
      (alpha_lexical_lt (u ++ t) t → ¬ alpha_lexical_lt t (u ++ u ++ t)) ∧
      (alpha_lexical_lt t (u ++ t) → ¬ alpha_lexical_lt (u ++ u ++ t) t) := by
  have hpar : ∀ x y : List ℕ, alpha_lexical_lt (u ++ x) (u ++ y) ↔ alpha_lexical_lt y x := by
    intro x y
    rw [alpha_lexical_lt_append_parity]
    simp [hodd]
  have hlen : 0 < u.length := by omega
  intro t
  induction hn : t.length using Nat.strong_induction_on generalizing t with
  | _ n ih =>
  by_cases hall : ∀ j < u.length, alpha_signed_cell t j = alpha_signed_cell u j
  · -- t starts with u
    have hgt : ∀ j < u.length, j < t.length ∧ t.getD j 0 = u.getD j 0 := by
      intro j hj
      have hg := alpha_nosq_signed_inj _ _ _ (hall j hj)
      have hupos : 0 < u.getD j 0 := by
        rw [List.getD_eq_getElem _ _ hj]; exact hu _ (List.getElem_mem hj)
      refine ⟨?_, hg⟩
      by_contra hc
      push Not at hc
      rw [List.getD_eq_default _ _ hc] at hg
      omega
    have htake : t.take u.length = u := by
      apply List.ext_getElem
      · simp only [List.length_take]
        have := (hgt (u.length - 1) (by omega)).1
        omega
      · intro j h1 h2
        obtain ⟨ht, h⟩ := hgt j h2
        rw [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ h2] at h
        rw [List.getElem_take]; exact h
    set t' := t.drop u.length with ht'
    have htt : t = u ++ t' := by rw [← htake, List.take_append_drop]
    have hlt' : t'.length < n := by
      rw [← hn, htt, List.length_append]; omega
    obtain ⟨ih1, ih2⟩ := ih _ hlt' t' rfl
    rw [htt]
    simp only [List.append_assoc]
    constructor
    · intro h1 h2
      rw [hpar] at h1 h2
      exact ih2 h1 (by simpa [List.append_assoc] using h2)
    · intro h1 h2
      rw [hpar] at h1 h2
      exact ih1 h1 (by simpa [List.append_assoc] using h2)
  · push Not at hall
    classical
    let P : ℕ → Prop := fun p => p < u.length ∧ alpha_signed_cell t p ≠ alpha_signed_cell u p
    have hex : ∃ p, P p := hall
    let p := Nat.find hex
    have hp : P p := Nat.find_spec hex
    have hmin : ∀ j < p, alpha_signed_cell t j = alpha_signed_cell u j := by
      intro j hj
      by_contra hne
      exact Nat.find_min hex hj ⟨lt_trans hj hp.1, hne⟩
    have hA : ∀ X : List ℕ, ∀ j ≤ p, alpha_signed_cell (u ++ X) j = alpha_signed_cell u j :=
      fun X j hj => alpha_nosq_signed_append_left u X j (lt_of_le_of_lt hj hp.1)
    have k1 : alpha_lexical_lt (u ++ t) t ↔ alpha_signed_cell u p < alpha_signed_cell t p := by
      rw [alpha_nosq_lt_iff_first_diff _ _ p, hA t p le_rfl]
      · intro j hj; rw [hA t j hj.le, hmin j hj]
      · rw [hA t p le_rfl]; exact fun h => hp.2 h.symm
    have k2 : alpha_lexical_lt t (u ++ u ++ t) ↔ alpha_signed_cell t p < alpha_signed_cell u p := by
      rw [List.append_assoc, alpha_nosq_lt_iff_first_diff _ _ p, hA _ p le_rfl]
      · intro j hj; rw [hA _ j hj.le, hmin j hj]
      · rw [hA _ p le_rfl]; exact hp.2
    have k3 : alpha_lexical_lt t (u ++ t) ↔ alpha_signed_cell t p < alpha_signed_cell u p := by
      rw [alpha_nosq_lt_iff_first_diff _ _ p, hA t p le_rfl]
      · intro j hj; rw [hA t j hj.le, hmin j hj]
      · rw [hA t p le_rfl]; exact hp.2
    have k4 : alpha_lexical_lt (u ++ u ++ t) t ↔ alpha_signed_cell u p < alpha_signed_cell t p := by
      rw [List.append_assoc, alpha_nosq_lt_iff_first_diff _ _ p, hA _ p le_rfl]
      · intro j hj; rw [hA _ j hj.le, hmin j hj]
      · rw [hA _ p le_rfl]; exact fun h => hp.2 h.symm
    rw [k1, k2, k3, k4]
    exact ⟨fun h1 h2 => lt_asymm h1 h2, fun h1 h2 => lt_asymm h1 h2⟩

theorem alpha_lexical_no_odd_square_prefix (u tail : List ℕ) (hodd : u.length % 2 = 1) : ¬ alpha_is_lexical (u ++ u ++ tail) := by
  rintro ⟨_, hpos, hlex⟩
  have hu : ∀ v ∈ u, 0 < v := fun v hv => hpos v (by simp [hv])
  have hlen : 0 < u.length := by omega
  have hpar : ∀ x y : List ℕ, alpha_lexical_lt (u ++ x) (u ++ y) ↔ alpha_lexical_lt y x := by
    intro x y
    rw [alpha_lexical_lt_append_parity]
    simp [hodd]
  have F1 := hlex u.length (by simp; omega) hlen
  rw [List.append_assoc, List.drop_left, hpar] at F1
  rcases tail with _ | ⟨x, xs⟩
  · rw [List.append_nil] at F1
    have h0 : 0 < u.getD 0 0 := by
      rw [List.getD_eq_getElem _ _ hlen]; exact hu _ (List.getElem_mem hlen)
    have e1 : alpha_signed_cell u 0 = (u.getD 0 0 : ℤ) := by simp [alpha_signed_cell]
    have e2 : alpha_signed_cell ([] : List ℕ) 0 = 0 := by simp [alpha_signed_cell]
    rw [alpha_nosq_lt_iff_first_diff _ _ 0 (by intro j hj; omega) (by rw [e1, e2]; omega),
      e1, e2] at F1
    omega
  · have F2 := hlex (u.length + u.length) (by simp) (by omega)
    
    have hd : (u ++ u ++ (x :: xs)).drop (u.length + u.length) = x :: xs := by
      rw [List.append_assoc]; simp
    rw [hd] at F2
    exact (alpha_nosq_core u hu hodd (x :: xs)).1 F1 F2
