import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDeviationMonoInsideDrop
import AFTD.Kb.GameTheoryEconomics.MaxcutDeviationInternalColorCountLt
import AFTD.Kb.GameTheoryEconomics.MaxcutDeviationDegreeSumGe
import AFTD.Kb.GameTheoryEconomics.MaxcutOp89ExistsOfCardLe
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_op89_exists_of_card_le_two_mul_add_one

Topic: equilibria   Node: 0273988ce72d

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

For every integer k ≥ 3 and every finite simple graph G on at most 2k+1 vertices, the unweighted Max-k-Cut game on (G,k) admits an optimal colouring that is a strong equilibrium. This strictly extends maxcut_op89_exists_of_card_le (n ≤ 2k) to the boundary case n = 2k+1, which is a genuine new case of OP-89.
-/

/-- For every k ≥ 3 and every finite simple graph on at most 2k+1 vertices, the Max-k-Cut game has an optimal colouring that is a strong equilibrium. -/
theorem maxcut_op89_exists_of_card_le_two_mul_add_one {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k)
    (hV : Fintype.card V ≤ 2 * k + 1) : maxcut_has_optimal_strong_equilibrium G k := by
  classical
  by_cases h2 : Fintype.card V ≤ 2 * k
  · exact maxcut_op89_exists_of_card_le V G k hk h2
  have hcard : Fintype.card V = 2 * k + 1 := by omega
  have hk0 : 0 < k := by omega
  haveI : Nonempty (V → Fin k) := ⟨fun _ => ⟨0, hk0⟩⟩
  obtain ⟨σ, hσopt⟩ := Finite.exists_max (maxcut_welfare G (k := k))
  refine ⟨σ, hσopt, ?_⟩
  intro S τ hdev
  have hdeg_le : ∀ v, G.degree v ≤ 2 * k := by
    intro v
    have := G.degree_lt_card_verts v
    omega
  set mf : V → ℕ := fun v => (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card with hmf
  have hmono_le : ∀ v, k * mf v ≤ G.degree v := by
    intro v
    simp only [hmf]
    have hsum : (Finset.univ.filter fun w => G.Adj v w).card =
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := Finset.univ)
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
      simp only [Finset.filter_filter]
    have hdv : (Finset.univ.filter fun w => G.Adj v w).card = G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    have hlow : ∑ _c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card :=
      Finset.sum_le_sum fun c _ => maxcut_optimal_same_color_le G σ hσopt v c
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlow
    omega
  have hdeg_eq : ∀ v ∈ S, G.degree v = 2 * k := by
    have h1 : 2 * k * S.card ≤ ∑ v ∈ S, G.degree v := maxcut_deviation_degree_sum_ge G σ τ S hσopt hdev
    have h2 : ∑ v ∈ S, G.degree v ≤ ∑ v ∈ S, (2 * k) := Finset.sum_le_sum fun v _ => hdeg_le v
    have h3 : ∑ v ∈ S, (2 * k) = 2 * k * S.card := by
      rw [Finset.sum_const, smul_eq_mul]
      ring
    have h4 : ∑ v ∈ S, G.degree v = ∑ v ∈ S, (2 * k) := by omega
    exact (Finset.sum_eq_sum_iff_of_le (s := S) (f := fun v => G.degree v) (g := fun _ => 2 * k)
      (fun v _ => hdeg_le v)).1 h4
  have huniv : ∀ v ∈ S, G.IsUniversal v := by
    intro v hv
    have h1 := hdeg_eq v hv
    rw [← SimpleGraph.degree_eq_card_sub_one]
    omega
  have hadj : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → G.Adj v w := by
    intro v hv w hw hne
    exact huniv v hv hne
  set M : ℕ := ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) with hM
  set X : ℕ := ∑ v ∈ S, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) with hX
  have hsplit : ∑ v ∈ S, mf v = M + X := by
    rw [hM, hX]
    simp only [hmf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter,
      Finset.sum_add_sum_compl S (fun w => if G.Adj v w ∧ σ w = σ v then 1 else 0)]
  have hm_le_two : ∀ v, mf v ≤ 2 := by
    intro v
    have h1 := hmono_le v
    have h2 := hdeg_le v
    have h3 : k * mf v ≤ k * 2 := by omega
    exact Nat.le_of_mul_le_mul_left h3 hk0
  have hsum_m : ∑ v ∈ S, mf v ≤ 2 * S.card := by
    have h1 : ∑ v ∈ S, mf v ≤ ∑ v ∈ S, (2 : ℕ) := Finset.sum_le_sum fun v _ => hm_le_two v
    have h2 : ∑ v ∈ S, (2 : ℕ) = 2 * S.card := by
      rw [Finset.sum_const, smul_eq_mul]
      ring
    omega
  have hM_ge : 2 * S.card ≤ M := by
    rw [hM]
    have h1 := maxcut_deviation_mono_inside_drop G σ τ S hσopt hdev
    omega
  have hMX : M + X ≤ 2 * S.card := by rw [← hsplit]; exact hsum_m
  have hM_eq : M = 2 * S.card := by omega
  have hX0 : X = 0 := by omega
  have hm_eq_two : ∀ v ∈ S, mf v = 2 := by
    have h1 : ∑ v ∈ S, mf v = ∑ v ∈ S, (2 : ℕ) := by
      have h2 : ∑ v ∈ S, (2 : ℕ) = 2 * S.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
      rw [h2, hsplit, hM_eq, hX0]
      omega
    exact (Finset.sum_eq_sum_iff_of_le (s := S) (f := mf) (g := fun _ => 2)
      (fun v _ => hm_le_two v)).1 h1
  have hX_v : ∀ v ∈ S, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) = 0 := by
    rw [hX] at hX0
    exact Finset.sum_eq_zero_iff.mp hX0
  have hno_out : ∀ v ∈ S, ∀ w, w ∉ S → G.Adj v w → σ w ≠ σ v := by
    intro v hv w hw hadjv hcol
    have h2 := hX_v v hv
    have h3 : (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) = 0 :=
      Finset.sum_eq_zero_iff.mp h2 w (Finset.mem_compl.mpr hw)
    rw [if_pos (by exact ⟨hadjv, hcol⟩)] at h3
    exact absurd h3 (by norm_num)
  have hmono_fiber : ∀ v ∈ S,
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) = (S.filter fun w => σ w = σ v).erase v := by
    intro v hv
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨ha, hc⟩
      refine ⟨?_, ?_, hc⟩
      · rintro rfl
        exact G.irrefl ha
      · by_contra hw
        exact hno_out v hv w hw ha hc
    · rintro ⟨hne, hwS, hc⟩
      exact ⟨hadj v hv w hwS (Ne.symm hne), hc⟩
  have hfiber3 : ∀ v ∈ S, (S.filter fun w => σ w = σ v).card = 3 := by
    intro v hv
    have h1 := hmono_fiber v hv
    have h2 : mf v = 2 := hm_eq_two v hv
    have hm2 : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 := by
      simpa only [hmf] using h2
    have h3 : v ∈ S.filter fun w => σ w = σ v := Finset.mem_filter.mpr ⟨hv, rfl⟩
    have hpos : 0 < (S.filter fun w => σ w = σ v).card := Finset.card_pos.mpr ⟨v, h3⟩
    have h4 : (S.filter fun w => σ w = σ v).card - 1 = 2 := by
      rw [← Finset.card_erase_of_mem h3, ← h1, hm2]
    omega
  have hcardS : S.card = (S.image σ).card * 3 := by
    have hmaps : Set.MapsTo σ ↑S ↑(S.image σ) := fun x hx => Finset.mem_image_of_mem σ hx
    have h1 := Finset.card_eq_sum_card_fiberwise (f := σ) (s := S) (t := S.image σ) hmaps
    have h3 : ∑ b ∈ S.image σ, (S.filter fun w => σ w = b).card = ∑ b ∈ S.image σ, (3 : ℕ) :=
      Finset.sum_congr rfl fun b hb => by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        exact hfiber3 v hv
    rw [h1, h3, Finset.sum_const, smul_eq_mul]
  have hMtau : (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ)) = 0 := by
    have h1 := maxcut_deviation_mono_inside_drop G σ τ S hσopt hdev
    rw [hM] at hM_eq
    omega
  have hMtau_v : ∀ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ) = 0 :=
    fun v hv => Finset.sum_eq_zero_iff.mp hMtau v hv
  have hinj_tau : Set.InjOn τ ↑S := by
    intro a ha b hb hab
    by_contra hne
    have hmem : b ∈ S.filter fun w => G.Adj a w ∧ τ w = τ a := by
      simp only [Finset.mem_filter]
      exact ⟨hb, hadj a ha b hb hne, hab.symm⟩
    have hpos : 0 < (S.filter fun w => G.Adj a w ∧ τ w = τ a).card := Finset.card_pos.mpr ⟨b, hmem⟩
    have hzero : (S.filter fun w => G.Adj a w ∧ τ w = τ a).card = 0 := by
      rw [Finset.card_filter]
      exact hMtau_v a ha
    omega
  have himage_tau : (S.image τ).card = S.card := Finset.card_image_of_injOn hinj_tau
  have hsubset : S.image τ ⊆ S.image σ := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    have hlt := maxcut_deviation_internal_color_count_lt G σ τ S hσopt hdev hv
    have hzero : (S.filter fun w => G.Adj v w ∧ τ w = τ v).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨w, hw⟩
      simp only [Finset.mem_filter] at hw
      have h1 : w = v := hinj_tau hw.1 hv hw.2.2
      rw [h1] at hw
      exact G.irrefl hw.2.1
    have hpos : 0 < (S.filter fun w => G.Adj v w ∧ σ w = τ v).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter] at hw
    rw [← hw.2.2]
    exact Finset.mem_image_of_mem σ hw.1
  have hle : S.card ≤ (S.image σ).card := by
    rw [← himage_tau]
    exact Finset.card_le_card hsubset
  have hp : 0 < S.card := Finset.card_pos.mpr hdev.1
  rw [hcardS] at hle
  omega
