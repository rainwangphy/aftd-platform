import AFTD.Prelude
import AFTD.Kb.Tcs.IsDominatingDistribution
import AFTD.Kb.Tcs.IsForwardBiasedOptimal
import AFTD.Kb.Tcs.IsForwardBiasedSelectorOutput
import AFTD.Kb.Tcs.LpCoordRefine
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ForwardBiasedSelectorOutputUnique

/-!
# forward_biased_selector_dominating_and_computable

Topic: online_algorithms   Node: d12f67a67d26

Provenance: formalization of a published result. Source: arXiv:2610.40824 Proposition 7

On every Markov paging instance with n pages, cache C, fault on page s, and hitting probabilities α, assuming the dominating distribution feasible region is nonempty, the forward-biased selector outputs a unique distribution μ that is dominating, is the unique lexicographically largest optimal solution to the forward-biased linear program maximizing μ ((s + 1) mod n), and is computed by the sequence of |C| + 1 linear programs given by coordinate refinement.
-/

open Set in
private lemma forward_biased_selector_dominating_and_computable_aux
    {n : ℕ} (C : Finset (Fin n)) (e : Fin n)
    (α : Fin n → Fin n → ℝ)
    (hfeas : ∃ μ, is_dominating_distribution C α μ) :
    ∃! μ, is_dominating_distribution C α μ ∧
      is_forward_biased_selector_output C α e μ ∧
      lp_coord_refine {ν | is_forward_biased_optimal C α e ν} (C.sort (· ≤ ·)) C.card = {μ} := by
  classical
  set D : Set (Fin n → ℝ) := {μ | is_dominating_distribution C α μ} with hD
  set K : Set (Fin n → ℝ) := {ν | is_forward_biased_optimal C α e ν} with hK
  set L : List (Fin n) := C.sort (· ≤ ·) with hL
  set S : ℕ → Set (Fin n → ℝ) := fun m => lp_coord_refine K L m with hS
  have hLlen : L.length = C.card := by rw [hL]; exact Finset.length_sort (· ≤ ·)
  have hDcompact : IsCompact D := by
    rw [hD]
    have hclosed : IsClosed {μ : Fin n → ℝ | is_dominating_distribution C α μ} := by
      have h1 : IsClosed {μ : Fin n → ℝ | ∀ p, 0 ≤ μ p} := by
        rw [show {μ : Fin n → ℝ | ∀ p, 0 ≤ μ p} = ⋂ p, {μ : Fin n → ℝ | 0 ≤ μ p} by
          ext μ; simp]
        exact isClosed_iInter (fun p => isClosed_le continuous_const (continuous_apply p))
      have h2 : IsClosed {μ : Fin n → ℝ | ∑ p, μ p = 1} :=
        isClosed_eq (by fun_prop) continuous_const
      have h3 : IsClosed {μ : Fin n → ℝ | ∀ p ∉ C, μ p = 0} := by
        rw [show {μ : Fin n → ℝ | ∀ p ∉ C, μ p = 0} = ⋂ p, ⋂ (_ : p ∉ C), {μ : Fin n → ℝ | μ p = 0} by
          ext μ; simp]
        exact isClosed_iInter (fun p => isClosed_iInter (fun _ => isClosed_eq (continuous_apply p) continuous_const))
      have h4 : IsClosed {μ : Fin n → ℝ | ∀ q ∈ C, ∑ p ∈ C, μ p * α p q ≤ 1/2} := by
        rw [show {μ : Fin n → ℝ | ∀ q ∈ C, ∑ p ∈ C, μ p * α p q ≤ 1/2} =
            ⋂ q, ⋂ (_ : q ∈ C), {μ : Fin n → ℝ | ∑ p ∈ C, μ p * α p q ≤ 1/2} by
          ext μ; simp]
        exact isClosed_iInter (fun q => isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const))
      have hDeq : {μ : Fin n → ℝ | is_dominating_distribution C α μ} =
          {μ : Fin n → ℝ | ∀ p, 0 ≤ μ p} ∩ ({μ : Fin n → ℝ | ∑ p, μ p = 1} ∩
            ({μ : Fin n → ℝ | ∀ p ∉ C, μ p = 0} ∩ {μ : Fin n → ℝ | ∀ q ∈ C, ∑ p ∈ C, μ p * α p q ≤ 1/2})) := by
        ext μ; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, is_dominating_distribution]
      rw [hDeq]
      exact h1.inter (h2.inter (h3.inter h4))
    refine IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (Fin n)) hclosed ?_
    intro μ hμ; exact ⟨hμ.1, hμ.2.1⟩
  have hDne : D.Nonempty := by
    obtain ⟨μ0, hμ0⟩ := hfeas
    exact ⟨μ0, by rw [hD]; exact hμ0⟩
  have hKne : K.Nonempty := by
    obtain ⟨x, hx, hmax⟩ := hDcompact.exists_isMaxOn hDne (continuous_apply e).continuousOn
    rw [hK]
    refine ⟨x, ?_, ?_⟩
    · rw [hD] at hx; exact hx
    · intro ν hν
      exact hmax (by rw [hD]; exact hν)
  have hKD : K ⊆ D := by
    intro x hx; rw [hK] at hx; rw [hD]; exact hx.1
  have hKcompact : IsCompact K := by
    have hKclosed : IsClosed K := by
      rw [hK]
      have hKeq : {ν : Fin n → ℝ | is_forward_biased_optimal C α e ν} =
          D ∩ (⋂ η ∈ D, {ν : Fin n → ℝ | η e ≤ ν e}) := by
        rw [hD]
        ext ν; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, is_forward_biased_optimal]
      rw [hKeq]
      exact hDcompact.isClosed.inter (isClosed_biInter fun η _ => isClosed_le continuous_const (continuous_apply e))
    exact IsCompact.of_isClosed_subset hDcompact hKclosed hKD
  have hstep : ∀ m, S (m+1) = (if h : m < L.length then
      {μ | μ ∈ S m ∧ ∀ ν ∈ S m, ν (L.get ⟨m,h⟩) ≤ μ (L.get ⟨m,h⟩)} else S m) := by
    intro m; rw [hS]; simp [lp_coord_refine]
  have hstep_sub : ∀ m, S (m+1) ⊆ S m := by
    intro m
    rw [hstep m]
    by_cases h : m < L.length
    · rw [dif_pos h]; intro x hx; exact hx.1
    · rw [dif_neg h]
  have hmono : ∀ {a b : ℕ}, a ≤ b → S b ⊆ S a := by
    intro a b hab
    induction b with
    | zero =>
      have ha0 : a = 0 := Nat.le_zero.mp hab
      rw [ha0]
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [← h]
      · exact (hstep_sub b).trans (ih (by omega))
  have hind : ∀ m ≤ C.card, (S m).Nonempty ∧ IsCompact (S m) ∧ S m ⊆ K := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · simpa [hS, lp_coord_refine] using hKne
      · simpa [hS, lp_coord_refine] using hKcompact
      · simp [hS, lp_coord_refine]
    | succ m ih =>
      intro hm
      have hmL : m < L.length := by omega
      obtain ⟨hne, hcomp, hsubK⟩ := ih (by omega)
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨x, hx, hmax⟩ := hcomp.exists_isMaxOn hne (continuous_apply (L.get ⟨m, hmL⟩)).continuousOn
        refine ⟨x, ?_⟩
        rw [hstep m, dif_pos hmL]
        exact ⟨hx, fun ν hν => hmax hν⟩
      · rw [hstep m, dif_pos hmL]
        have hclosed : IsClosed {μ : Fin n → ℝ | μ ∈ S m ∧ ∀ ν ∈ S m, ν (L.get ⟨m,hmL⟩) ≤ μ (L.get ⟨m,hmL⟩)} := by
          have heq : {μ : Fin n → ℝ | μ ∈ S m ∧ ∀ ν ∈ S m, ν (L.get ⟨m,hmL⟩) ≤ μ (L.get ⟨m,hmL⟩)}
              = S m ∩ (⋂ ν ∈ S m, {μ : Fin n → ℝ | ν (L.get ⟨m,hmL⟩) ≤ μ (L.get ⟨m,hmL⟩)}) := by
            ext μ; simp
          rw [heq]
          exact hcomp.isClosed.inter (isClosed_biInter fun ν _ => isClosed_le continuous_const (continuous_apply _))
        exact IsCompact.of_isClosed_subset hcomp hclosed (fun x hx => hx.1)
      · exact (hstep_sub m).trans hsubK
  obtain ⟨hSkne, hSkcomp, hSkK⟩ := hind C.card le_rfl
  have hSD : S C.card ⊆ D := hSkK.trans hKD
  have hkey : ∀ (j : ℕ) (hj : j < L.length) (a b : Fin n → ℝ), a ∈ S (j+1) → b ∈ S (j+1) →
      a (L.get ⟨j,hj⟩) = b (L.get ⟨j,hj⟩) := by
    intro j hj a b ha hb
    have ha' := ha; have hb' := hb
    rw [hstep j, dif_pos hj] at ha' hb'
    exact le_antisymm (hb'.2 a ha'.1) (ha'.2 b hb'.1)
  have hall_eq : ∀ μ ∈ S C.card, ∀ ν ∈ S C.card, μ = ν := by
    intro μ hμ ν hν
    funext p
    by_cases hp : p ∈ C
    · have hpL : p ∈ L := by rw [hL]; exact (Finset.mem_sort (· ≤ ·)).mpr hp
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hpL
      have h := hkey j hj μ ν (hmono (by omega : j+1 ≤ C.card) hμ) (hmono (by omega : j+1 ≤ C.card) hν)
      rw [List.get_eq_getElem] at h
      rw [hjeq] at h
      exact h
    · have hμD : is_dominating_distribution C α μ := by have := hSD hμ; rw [hD] at this; exact this
      have hνD : is_dominating_distribution C α ν := by have := hSD hν; rw [hD] at this; exact this
      rw [hμD.2.2.1 p hp, hνD.2.2.1 p hp]
  have hlex : ∀ μ ∈ S C.card, ∀ ν ∈ K, ν = μ ∨ Pi.Lex (fun x1 x2 : Fin n => x1 < x2) (fun {i} x1 x2 => x1 < x2) ν μ := by
    intro μ hμ ν hνK
    by_cases hνS : ν ∈ S C.card
    · exact Or.inl (hall_eq ν hνS μ hμ)
    · right
      have hνS0 : ν ∈ S 0 := by rw [hS]; simpa [lp_coord_refine] using hνK
      have hpos : 0 < C.card := by
        rcases Nat.eq_zero_or_pos C.card with h | h
        · rw [h] at hνS; exact absurd hνS0 hνS
        · exact h
      have hex : ∃ k, ν ∉ S (k+1) := ⟨C.card - 1, by rw [Nat.sub_add_cancel hpos]; exact hνS⟩
      set m := Nat.find hex with hmdef
      have hm_spec : ν ∉ S (m+1) := by rw [hmdef]; exact Nat.find_spec hex
      have hm_lt : m < C.card := by
        have h1 : m ≤ C.card - 1 := by
          rw [hmdef]; exact Nat.find_min' hex (by rw [Nat.sub_add_cancel hpos]; exact hνS)
        omega
      have hmL : m < L.length := by omega
      have hmin : ∀ j, j < m → ν ∈ S (j+1) := by
        intro j hj
        have hh := Nat.find_min hex (show j < Nat.find hex by rw [← hmdef]; exact hj)
        simpa using hh
      have hνSm : ν ∈ S m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos'
        · rw [h0]; exact hνS0
        · have hh := hmin (m-1) (by omega)
          rwa [Nat.sub_add_cancel hpos'] at hh
      have hν_not : ¬ (∀ η ∈ S m, η (L.get ⟨m,hmL⟩) ≤ ν (L.get ⟨m,hmL⟩)) := by
        intro hcon
        exact hm_spec (by rw [hstep m, dif_pos hmL]; exact ⟨hνSm, hcon⟩)
      obtain ⟨η, hηS, hνη⟩ : ∃ η, η ∈ S m ∧ ν (L.get ⟨m,hmL⟩) < η (L.get ⟨m,hmL⟩) := by
        by_contra hc
        push Not at hc
        exact hν_not hc
      have hμS1 : μ ∈ S (m+1) := hmono (by omega : m+1 ≤ C.card) hμ
      have hμmax : ∀ η ∈ S m, η (L.get ⟨m,hmL⟩) ≤ μ (L.get ⟨m,hmL⟩) := by
        have := hμS1; rw [hstep m, dif_pos hmL] at this; exact this.2
      have hp_lt : ν (L.get ⟨m,hmL⟩) < μ (L.get ⟨m,hmL⟩) := lt_of_lt_of_le hνη (hμmax η hηS)
      refine ⟨L.get ⟨m,hmL⟩, ?_, hp_lt⟩
      intro q hq
      by_cases hqC : q ∈ C
      · have hqL : q ∈ L := by rw [hL]; exact (Finset.mem_sort (· ≤ ·)).mpr hqC
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hqL
        have hjm : j < m := by
          by_contra hjm
          push Not at hjm
          have hpw : List.Pairwise (· ≤ ·) L := by rw [hL]; exact Finset.pairwise_sort C (· ≤ ·)
          have hle : L.get ⟨m, hmL⟩ ≤ L.get ⟨j, hj⟩ := by
            rcases lt_or_eq_of_le hjm with hlt | heq
            · have := (List.pairwise_iff_getElem.mp hpw) m j hmL hj hlt
              rwa [List.get_eq_getElem, List.get_eq_getElem]
            · have h1 : (⟨m, hmL⟩ : Fin L.length) = ⟨j, hj⟩ := Fin.ext heq
              rw [h1]
          have hleq : L.get ⟨m, hmL⟩ ≤ q := by rw [← hjeq]; exact hle
          exact absurd hq (not_lt.mpr hleq)
        have heqj : L.get ⟨j, hj⟩ = q := by rw [List.get_eq_getElem]; exact hjeq
        have h := hkey j hj ν μ (hmin j hjm) (hmono (by omega : j+1 ≤ C.card) hμ)
        rw [heqj] at h
        exact h
      · have hμD : is_dominating_distribution C α μ := by have := hSD hμ; rw [hD] at this; exact this
        have hνD : is_dominating_distribution C α ν := by rw [hK] at hνK; exact hνK.1
        rw [hμD.2.2.1 q hqC, hνD.2.2.1 q hqC]
  obtain ⟨μstar, hμstar⟩ := hSkne
  have hSk_eq : S C.card = {μstar} := by
    ext x
    constructor
    · intro hx; exact hall_eq x hx μstar hμstar
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hμstar
  have hμstarK : μstar ∈ K := hSkK hμstar
  have hμstarD : is_dominating_distribution C α μstar := by
    have := hSD hμstar; rw [hD] at this; exact this
  have hμstar_opt : is_forward_biased_optimal C α e μstar := by rw [hK] at hμstarK; exact hμstarK
  have hsel : is_forward_biased_selector_output C α e μstar := by
    refine ⟨hμstar_opt, ?_⟩
    intro ν hν
    exact hlex μstar hμstar ν (by rw [hK]; exact hν)
  have hrefine : lp_coord_refine {ν | is_forward_biased_optimal C α e ν} (C.sort (· ≤ ·)) C.card = {μstar} := by
    rw [← hK, ← hL]
    simpa [hS] using hSk_eq
  refine ⟨μstar, ⟨hμstarD, hsel, hrefine⟩, ?_⟩
  rintro y ⟨hyD, hySel, hyRef⟩
  exact forward_biased_selector_output_unique hySel hsel

/-- Proposition 7: The forward-biased selector outputs a dominating distribution computable by at most |C| + 1 linear programs. -/
theorem forward_biased_selector_dominating_and_computable
    {n : ℕ} (hn : 0 < n) (C : Finset (Fin n)) (s : Fin n)
    (α : Fin n → Fin n → ℝ)
    (hfeas : ∃ μ, is_dominating_distribution C α μ) :
    ∃! μ, is_dominating_distribution C α μ ∧
      is_forward_biased_selector_output C α ⟨(s.val + 1) % n, Nat.mod_lt _ hn⟩ μ ∧
      lp_coord_refine {ν | is_forward_biased_optimal C α ⟨(s.val + 1) % n, Nat.mod_lt _ hn⟩ ν}
        (C.sort (· ≤ ·)) C.card = {μ} := by
  exact forward_biased_selector_dominating_and_computable_aux C ⟨(s.val + 1) % n, Nat.mod_lt _ hn⟩ α hfeas
