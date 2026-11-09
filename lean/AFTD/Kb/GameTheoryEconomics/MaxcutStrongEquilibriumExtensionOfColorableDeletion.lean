import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectOneStrongDeviationMonoDecreases
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_strong_equilibrium_extension_of_colorable_deletion

Topic: equilibria   Node: b6ebc1666e28

Provenance: helper lemma. Partial case of the favorable-equilibrium degree-below-2k extension route for OP-85.

If a vertex has degree below twice the number of colors and its deletion is k-colorable, then the original graph has a strong equilibrium whose restriction to the deletion is also strong.
-/

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_proper_is_se
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ : V → Fin k) (hprop : ∀ x y, G.Adj x y → σ x ≠ σ y) :
    is_maxcut_strong_equilibrium G σ := by
  intro C τ hdev
  have hdefect : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 1 := by
    intro v
    have : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _ ⟨hadj, heq⟩
      exact hprop v w hadj heq.symm
    rw [this, Finset.card_empty]
    exact zero_le_one
  have step := maxcut_defect_one_strong_deviation_mono_decreases G σ τ C hdefect hdev
  obtain ⟨v, w, hadj, heq, -⟩ := step.2
  exact hprop v w hadj heq

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_exists_color_le_one
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) (hd : G.degree v < 2 * k)
    (f : V → Fin k) :
    ∃ c : Fin k, (Finset.filter (fun w => G.Adj v w ∧ f w = c) Finset.univ).card ≤ 1 := by
  by_contra! h
  have hfiber : (G.neighborFinset v).card =
      ∑ c : Fin k, (Finset.filter (fun w => f w = c) (G.neighborFinset v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have h1 : ∑ c : Fin k, 2 ≤ ∑ c : Fin k, (Finset.filter (fun w => f w = c) (G.neighborFinset v)).card := by
    apply Finset.sum_le_sum
    intro c _
    have heq : (Finset.filter (fun w => f w = c) (G.neighborFinset v)) =
               (Finset.filter (fun w => G.Adj v w ∧ f w = c) Finset.univ) := by
      ext w
      simp [SimpleGraph.mem_neighborFinset]
    rw [heq]
    have hc := h c
    omega
  have hsum : (∑ _c : Fin k, 2) = 2 * k := by simp [mul_comm]
  rw [hsum] at h1
  rw [G.card_neighborFinset_eq_degree] at hfiber
  omega

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_tau_proper
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {k : ℕ} (σ τ : V → Fin k) (C : Finset V)
    (hdefect : ∀ u : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card ≤ 1)
    (hdev : is_maxcut_strong_deviation G σ C τ)
    (h_mono_edge : ∀ x y, G.Adj x y → σ x = σ y → x = v ∨ y = v) :
    ∀ x y, G.Adj x y → τ x ≠ τ y := by
  have step := maxcut_defect_one_strong_deviation_mono_decreases G σ τ C hdefect hdev
  obtain ⟨v₀, w₀, hadj₀, hσ₀, hτ₀⟩ := step.2
  have hcard_v := hdefect v
  have h_unique : ∀ a b, a ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) →
                          b ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) → a = b := by
    intro a b ha hb
    have hsub : {a, b} ⊆ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    have hle := le_trans this hcard_v
    by_contra hab
    have : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
    omega
  intro x y hadj hτ_eq
  have hσ_xy := step.1 x y hadj hτ_eq
  have h_cases_xy := h_mono_edge x y hadj hσ_xy
  have h_cases_0 := h_mono_edge v₀ w₀ hadj₀ hσ₀
  have mem_M : ∀ a b, G.Adj a b → σ a = σ b → a = v →
      b ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := by
    intro a b hab hσ ha
    subst ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hab, hσ.symm⟩
  rcases h_cases_xy with hx | hy <;> rcases h_cases_0 with hv0 | hw0
  · have hy' : y ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M x y hadj hσ_xy hx
    have hw' : w₀ ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M v₀ w₀ hadj₀ hσ₀ hv0
    have : y = w₀ := h_unique y w₀ hy' hw'
    have : τ x = τ v₀ := by rw [hx, hv0]
    have : τ y = τ w₀ := by rw [‹y = w₀›]
    omega
  · have hy' : y ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M x y hadj hσ_xy hx
    have hv' : v₀ ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M w₀ v₀ hadj₀.symm hσ₀.symm hw0
    have : y = v₀ := h_unique y v₀ hy' hv'
    have : τ x = τ w₀ := by rw [hx, hw0]
    have : τ y = τ v₀ := by rw [‹y = v₀›]
    omega
  · have hx' : x ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M y x hadj.symm hσ_xy.symm hy
    have hw' : w₀ ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M v₀ w₀ hadj₀ hσ₀ hv0
    have : x = w₀ := h_unique x w₀ hx' hw'
    have : τ y = τ v₀ := by rw [hy, hv0]
    have : τ x = τ w₀ := by rw [‹x = w₀›]
    omega
  · have hx' : x ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M y x hadj.symm hσ_xy.symm hy
    have hv' : v₀ ∈ (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) := mem_M w₀ v₀ hadj₀.symm hσ₀.symm hw0
    have : x = v₀ := h_unique x v₀ hx' hv'
    have : τ y = τ w₀ := by rw [hy, hw0]
    have : τ x = τ v₀ := by rw [‹x = v₀›]
    omega

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_sigma_defect_le_one
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {k : ℕ} (c : Fin k)
    (s : (↑(Finset.univ.erase v) : Set V) → Fin k)
    (hprop : ∀ x y, (G.induce (↑(Finset.univ.erase v) : Set V)).Adj x y → s x ≠ s y)
    (hc : (Finset.univ.filter fun w => G.Adj v w ∧
      (if h : w = v then c else s ⟨w, Finset.mem_erase.mpr ⟨h, Finset.mem_univ w⟩⟩) = c).card ≤ 1) :
    let σ : V → Fin k := fun u =>
      if h : u = v then c else s ⟨u, Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩⟩
    ∀ u : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card ≤ 1 := by
  intro σ u
  by_cases hu : u = v
  · rw [hu]
    have heq : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) =
               (Finset.univ.filter fun w => G.Adj v w ∧
                 (if h : w = v then c else s ⟨w, Finset.mem_erase.mpr ⟨h, Finset.mem_univ w⟩⟩) = c) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : σ v = c := by dsimp [σ]; simp
      rw [this]
    rw [heq]
    exact hc
  · have hsub : (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u) ⊆ {v} := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_singleton]
      by_contra hwv
      have hu_sub : u ∈ (↑(Finset.univ.erase v) : Set V) := by
        simp [hu]
      have hw_sub : w ∈ (↑(Finset.univ.erase v) : Set V) := by
        simp [hwv]
      have hadj : (G.induce (↑(Finset.univ.erase v) : Set V)).Adj ⟨u, hu_sub⟩ ⟨w, hw_sub⟩ := hw.1
      have hdiff := hprop ⟨u, hu_sub⟩ ⟨w, hw_sub⟩ hadj
      have hσu : σ u = s ⟨u, hu_sub⟩ := by dsimp [σ]; simp [hu]
      have hσw : σ w = s ⟨w, hw_sub⟩ := by dsimp [σ]; simp [hwv]
      rw [hσu, hσw] at hw
      exact hdiff hw.2.symm
    exact le_trans (Finset.card_le_card hsub) (by simp)

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_sigma_mono_edge_incident_v
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {k : ℕ} (c : Fin k)
    (s : (↑(Finset.univ.erase v) : Set V) → Fin k)
    (hprop : ∀ x y, (G.induce (↑(Finset.univ.erase v) : Set V)).Adj x y → s x ≠ s y) :
    let σ : V → Fin k := fun u =>
      if h : u = v then c else s ⟨u, Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩⟩
    ∀ x y, G.Adj x y → σ x = σ y → x = v ∨ y = v := by
  intro σ x y hadj hσ
  by_contra! h
  have hx_sub : x ∈ (↑(Finset.univ.erase v) : Set V) := by simp [h.1]
  have hy_sub : y ∈ (↑(Finset.univ.erase v) : Set V) := by simp [h.2]
  have hadj' : (G.induce (↑(Finset.univ.erase v) : Set V)).Adj ⟨x, hx_sub⟩ ⟨y, hy_sub⟩ := hadj
  have hdiff := hprop ⟨x, hx_sub⟩ ⟨y, hy_sub⟩ hadj'
  have hσx : σ x = s ⟨x, hx_sub⟩ := by dsimp [σ]; simp [h.1]
  have hσy : σ y = s ⟨y, hy_sub⟩ := by dsimp [σ]; simp [h.2]
  rw [hσx, hσy] at hσ
  exact hdiff hσ

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion_restriction_is_s
    {V : Type} [Fintype V] [DecidableEq V] (v : V) {k : ℕ} (c : Fin k)
    (s : (↑(Finset.univ.erase v) : Set V) → Fin k) :
    let σ : V → Fin k := fun u =>
      if h : u = v then c else s ⟨u, Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩⟩
    (fun x : (↑(Finset.univ.erase v) : Set V) => σ x.1) = s := by
  intro σ
  funext ⟨x, hx⟩
  dsimp [σ]
  have hne : x ≠ v := (Finset.mem_erase.mp hx).1
  rw [dif_neg hne]

theorem maxcut_strong_equilibrium_extension_of_colorable_deletion
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) (hd : G.degree v < 2 * k)
    (hcolor : ∃ s : (↑(Finset.univ.erase v) : Set V) → Fin k,
      ∀ x y, (G.induce (↑(Finset.univ.erase v) : Set V)).Adj x y → s x ≠ s y) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ ∧
      is_maxcut_strong_equilibrium (G.induce (↑(Finset.univ.erase v) : Set V))
        (fun x : (↑(Finset.univ.erase v) : Set V) => σ x.1) := by
  obtain ⟨s, hs_prop⟩ := hcolor
  have hk : 0 < k := by omega
  let f : V → Fin k := fun u =>
    if h : u = v then ⟨0, hk⟩ else s ⟨u, Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩⟩
  obtain ⟨c, hc⟩ := maxcut_strong_equilibrium_extension_of_colorable_deletion_exists_color_le_one G v k hd f
  have hc' : (Finset.univ.filter fun w => G.Adj v w ∧
      (if h : w = v then c else s ⟨w, Finset.mem_erase.mpr ⟨h, Finset.mem_univ w⟩⟩) = c).card ≤ 1 := by
    have heq : (Finset.univ.filter fun w => G.Adj v w ∧
                 (if h : w = v then c else s ⟨w, Finset.mem_erase.mpr ⟨h, Finset.mem_univ w⟩⟩) = c) =
               (Finset.filter (fun w => G.Adj v w ∧ f w = c) Finset.univ) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hw : w = v
      · subst hw
        simp
      · dsimp [f]
        rw [dif_neg hw, dif_neg hw]
    rw [heq]
    exact hc
  let σ : V → Fin k := fun u =>
    if h : u = v then c else s ⟨u, Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩⟩
  have hdefect : ∀ u : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card ≤ 1 :=
    maxcut_strong_equilibrium_extension_of_colorable_deletion_sigma_defect_le_one G v c s hs_prop hc'
  have h_mono_edge : ∀ x y, G.Adj x y → σ x = σ y → x = v ∨ y = v :=
    maxcut_strong_equilibrium_extension_of_colorable_deletion_sigma_mono_edge_incident_v G v c s hs_prop
  by_cases hse : is_maxcut_strong_equilibrium G σ
  · refine ⟨σ, hse, ?_⟩
    have hrest := maxcut_strong_equilibrium_extension_of_colorable_deletion_restriction_is_s v c s
    rw [hrest]
    exact maxcut_strong_equilibrium_extension_of_colorable_deletion_proper_is_se (G.induce (↑(Finset.univ.erase v) : Set V)) s hs_prop
  · have hdev_ex : ∃ C τ, is_maxcut_strong_deviation G σ C τ := by
      simpa [is_maxcut_strong_equilibrium] using hse
    obtain ⟨C, τ, hdev⟩ := hdev_ex
    have htau_prop := maxcut_strong_equilibrium_extension_of_colorable_deletion_tau_proper G v σ τ C hdefect hdev h_mono_edge
    refine ⟨τ, maxcut_strong_equilibrium_extension_of_colorable_deletion_proper_is_se G τ htau_prop, ?_⟩
    apply maxcut_strong_equilibrium_extension_of_colorable_deletion_proper_is_se
    intro x y hadj
    exact htau_prop x.1 y.1 hadj
