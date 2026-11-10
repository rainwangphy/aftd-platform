import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongDeviationCarrier
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_two_color_strong_equilibrium_restricts_vertex

Topic: equilibria   Node: 4e5e592c45a2

Provenance: helper lemma. Two-color potential argument on the favorable-equilibrium vertex-extension route for OP-85.

For every finite graph and every vertex, a strong two-color equilibrium exists whose restriction after deleting that vertex is also strong; the vertex degree is arbitrary.
-/

open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
lemma maxcut_two_color_welfare_diff {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ τ : V → Fin 2) (S : Finset V)
    (hS_flip : ∀ v ∈ S, τ v ≠ σ v)
    (hS_same : ∀ v ∉ S, τ v = σ v) :
    maxcut_welfare G τ + 2 * ∑ v ∈ S, maxcut_utility G σ v =
      maxcut_welfare G σ + 2 * ∑ v ∈ S, maxcut_utility G τ v := by
  have hA : (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)) =
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    have hv_flip := hS_flip v hv
    have hw_flip := hS_flip w hw
    have hiff : (τ w ≠ τ v ↔ σ w ≠ σ v) := by
      revert hv_flip hw_flip
      generalize τ w = tw; generalize σ w = sw; generalize τ v = tv; generalize σ v = sv
      revert tw sw tv sv; decide
    simp only [hiff]
  have hC : (∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)) =
      ∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mem_compl] at hv hw
    rw [hS_same v hv, hS_same w hw]
  rw [maxcut_welfare_split G τ S, maxcut_welfare_split G σ S]
  rw [maxcut_utility_sum_split G τ S, maxcut_utility_sum_split G σ S]
  rw [hA, hC]
  omega

lemma maxcut_two_color_welfare_lt_of_flip {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ τ : V → Fin 2) (S : Finset V)
    (hS_flip : ∀ v ∈ S, τ v ≠ σ v)
    (hS_same : ∀ v ∉ S, τ v = σ v)
    (hut : ∀ v ∈ S, maxcut_utility G σ v < maxcut_utility G τ v) :
    maxcut_welfare G σ + 2 * S.card ≤ maxcut_welfare G τ := by
  have hdiff := maxcut_two_color_welfare_diff G σ τ S hS_flip hS_same
  have hsum : (∑ v ∈ S, maxcut_utility G σ v) + S.card ≤ ∑ v ∈ S, maxcut_utility G τ v := by
    have hcard : S.card = ∑ _ ∈ S, 1 := by simp
    rw [hcard, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x hx
    exact hut x hx
  omega

lemma maxcut_two_color_optimal_strong {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V → Fin 2) (hopt : is_maxcut_optimal G σ) :
    is_maxcut_strong_equilibrium G σ := by
  intro S τ hdev
  have hdev' := maxcut_strong_deviation_carrier G σ τ S hdev
  set S' := Finset.univ.filter fun v => τ v ≠ σ v
  have hS'_nonempty : S'.Nonempty := hdev'.1
  have hS'_flip : ∀ v ∈ S', τ v ≠ σ v := fun v hv => (Finset.mem_filter.mp hv).2
  have hS'_same : ∀ v ∉ S', τ v = σ v := by
    intro v hv
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
    exact hv
  have hut : ∀ v ∈ S', maxcut_utility G σ v < maxcut_utility G τ v := hdev'.2.2
  have hle := maxcut_two_color_welfare_lt_of_flip G σ τ S' hS'_flip hS'_same hut
  have hopt_le := hopt τ
  have hcard_pos : 0 < S'.card := Finset.Nonempty.card_pos hS'_nonempty
  omega

lemma maxcut_two_color_utility_G_eq_H_add {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) (v : V) (u : V) (hu : u ≠ v) :
    maxcut_utility G ρ u =
      maxcut_utility (G.induce (↑(Finset.univ.erase v) : Set V))
        (fun x => ρ x.1) ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩⟩ +
        (if G.Adj u v ∧ ρ v ≠ ρ u then 1 else 0) := by
  set s : Set V := (↑(Finset.univ.erase v) : Set V)
  set H := G.induce s
  let u_s : s := ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩⟩
  unfold maxcut_utility
  have hsplit : (Finset.univ : Finset V) = insert v (Finset.univ.erase v) := by
    exact (Finset.insert_erase (Finset.mem_univ v)).symm
  nth_rw 1 [hsplit]
  rw [Finset.filter_insert]
  have h_map : (Finset.filter (fun w => G.Adj u w ∧ ρ w ≠ ρ u) (Finset.univ.erase v)).card =
      (Finset.filter (fun w : s => H.Adj u_s w ∧ (fun x : s => ρ x.1) w ≠ (fun x : s => ρ x.1) u_s) Finset.univ).card := by
    rw [← Finset.card_map (Function.Embedding.subtype (· ∈ s))]
    congr 1
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]
    simp only [H, SimpleGraph.induce_adj, u_s, Finset.mem_erase, Finset.mem_univ, and_true,
      s, Finset.mem_coe]
    tauto
  split_ifs with h
  · rw [Finset.card_insert_of_notMem, h_map, add_comm]
    intro hmem
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hmem
    exact hmem.1 rfl
  · rw [add_zero, h_map]

theorem maxcut_two_color_strong_equilibrium_restricts_vertex
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) :
    ∃ σ : V → Fin 2, is_maxcut_strong_equilibrium G σ ∧
      is_maxcut_strong_equilibrium (G.induce (↑(Finset.univ.erase v) : Set V))
        (fun x : (↑(Finset.univ.erase v) : Set V) => σ x.1) := by
  set s : Set V := (↑(Finset.univ.erase v) : Set V)
  set H := G.induce s
  let f : (V → Fin 2) → Lex (ℕ × ℕ) := fun ρ =>
    toLex (maxcut_welfare G ρ, maxcut_welfare H (fun x : s => ρ x.1))
  have : Nonempty (V → Fin 2) := ⟨fun _ => 0⟩
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hmax : ∀ τ : V → Fin 2, f τ ≤ f σ := fun τ => hσ τ (Finset.mem_univ τ)
  have hopt : is_maxcut_optimal G σ := by
    intro τ
    have hle := hmax τ
    rw [Prod.Lex.toLex_le_toLex'] at hle
    exact hle.1
  refine ⟨σ, maxcut_two_color_optimal_strong G σ hopt, ?_⟩
  intro S_H τ_H hdev_H
  have hdev'_H := maxcut_strong_deviation_carrier H (fun x : s => σ x.1) τ_H S_H hdev_H
  set S'_H := Finset.univ.filter fun x : s => τ_H x ≠ σ x.1
  have hS'_H_nonempty : S'_H.Nonempty := hdev'_H.1
  have hS'_H_flip : ∀ x ∈ S'_H, τ_H x ≠ σ x.1 := fun x hx => (Finset.mem_filter.mp hx).2
  have hS'_H_same : ∀ x ∉ S'_H, τ_H x = σ x.1 := by
    intro x hx
    simp only [S'_H, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    exact hx
  have hut_H : ∀ x ∈ S'_H, maxcut_utility H (fun x : s => σ x.1) x < maxcut_utility H τ_H x := hdev'_H.2.2
  have hH_gain := maxcut_two_color_welfare_lt_of_flip H (fun x : s => σ x.1) τ_H S'_H hS'_H_flip hS'_H_same hut_H
  have hpos : 0 < S'_H.card := Finset.Nonempty.card_pos hS'_H_nonempty
  have hH_strict : maxcut_welfare H (fun x : s => σ x.1) < maxcut_welfare H τ_H := by omega
  let τ : V → Fin 2 := fun w =>
    if hw : w = v then σ v
    else τ_H ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩⟩
  have hτ_v : τ v = σ v := by dsimp [τ]; rw [dif_pos rfl]
  have hτ_s : ∀ x : s, τ x.1 = τ_H x := by
    intro ⟨w, hw⟩
    have hne : w ≠ v := (Finset.mem_erase.mp hw).1
    dsimp [τ]; rw [dif_neg hne]
  set S := Finset.univ.filter fun w => τ w ≠ σ w
  have hS_flip : ∀ w ∈ S, τ w ≠ σ w := fun w hw => (Finset.mem_filter.mp hw).2
  have hS_same : ∀ w ∉ S, τ w = σ w := by
    intro w hw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
    exact hw
  have hu_le : ∀ w ∈ S, maxcut_utility G σ w ≤ maxcut_utility G τ w := by
    intro w hw
    have hne : w ≠ v := by
      rintro rfl
      exact hS_flip w hw hτ_v
    let w_s : s := ⟨w, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w⟩⟩
    have hw_s_mem : w_s ∈ S'_H := by
      simp only [S'_H, Finset.mem_filter, Finset.mem_univ, true_and, w_s]
      rw [← hτ_s w_s]
      exact hS_flip w hw
    have h1 := maxcut_two_color_utility_G_eq_H_add G σ v w hne
    have h2 := maxcut_two_color_utility_G_eq_H_add G τ v w hne
    rw [hτ_v] at h2
    have h3 := hut_H w_s hw_s_mem
    change maxcut_utility G σ w = maxcut_utility H (fun x : s => σ x.1) w_s +
      (if G.Adj w v ∧ σ v ≠ σ w then 1 else 0) at h1
    change maxcut_utility G τ w = maxcut_utility H (fun x : s => τ x.1) w_s +
      (if G.Adj w v ∧ σ v ≠ τ w then 1 else 0) at h2
    have h4 : (fun x : s => τ x.1) = τ_H := funext hτ_s
    rw [h4] at h2
    have h1' : maxcut_utility G σ w ≤ maxcut_utility H (fun x : s => σ x.1) w_s + 1 := by
      rw [h1]; split_ifs <;> omega
    have h2' : maxcut_utility H τ_H w_s ≤ maxcut_utility G τ w := by
      rw [h2]; split_ifs <;> omega
    omega
  have hsum_le : (∑ w ∈ S, maxcut_utility G σ w) ≤ ∑ w ∈ S, maxcut_utility G τ w :=
    Finset.sum_le_sum hu_le
  have hdiff := maxcut_two_color_welfare_diff G σ τ S hS_flip hS_same
  have hG_ge : maxcut_welfare G σ ≤ maxcut_welfare G τ := by omega
  have hG_le : maxcut_welfare G τ ≤ maxcut_welfare G σ := hopt τ
  have hG_eq : maxcut_welfare G τ = maxcut_welfare G σ := le_antisymm hG_le hG_ge
  have hlex := hmax τ
  rw [Prod.Lex.toLex_le_toLex'] at hlex
  have hH_le := hlex.2 hG_eq
  have hτ_H_eq : (fun x : s => τ x.1) = τ_H := funext hτ_s
  rw [hτ_H_eq] at hH_le
  omega
