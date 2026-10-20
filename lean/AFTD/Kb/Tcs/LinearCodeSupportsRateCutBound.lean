import AFTD.Prelude
import AFTD.Kb.Tcs.CutSeparation
import AFTD.Kb.Tcs.CutCapacity
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CodeTransmissionsCrossCutLe
import AFTD.Kb.Tcs.CausalCodeValsZeroOutside
import AFTD.Kb.Tcs.CausalCodeValUnique
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.G

/-!
# linear_code_supports_rate_cut_bound

Topic: information   Node: 41e9cb995798

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

If a linear network code over a field F supports the common rate r on net with sessions sess, then for every vertex set S, r times the number of sessions crossing S is at most the total capacity leaving S.
-/

noncomputable def linear_code_supports_rate_cut_bound_code_val
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    {F : Type} [Field F] {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (msg : K → Fin code.L → F) :
    Fin code.M → F :=
  (code.correct msg).choose

theorem linear_code_supports_rate_cut_bound_code_val_recurrence
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    {F : Type} [Field F] {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (msg : K → Fin code.L → F) (m : Fin code.M) :
    linear_code_supports_rate_cut_bound_code_val code msg m =
      ∑ k, ∑ j, code.α m k j * msg k j + ∑ m', code.β m m' * linear_code_supports_rate_cut_bound_code_val code msg m' :=
  (code.correct msg).choose_spec.1 m

theorem linear_code_supports_rate_cut_bound_code_val_decode
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    {F : Type} [Field F] {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (msg : K → Fin code.L → F) (k : K) (j : Fin code.L) :
    msg k j = ∑ m, code.γ k j m * linear_code_supports_rate_cut_bound_code_val code msg m :=
  (code.correct msg).choose_spec.2 k j

theorem linear_code_supports_rate_cut_bound_code_val_add
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    {F : Type} [Field F] {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (msg msg' : K → Fin code.L → F) :
    linear_code_supports_rate_cut_bound_code_val code (msg + msg') =
      linear_code_supports_rate_cut_bound_code_val code msg + linear_code_supports_rate_cut_bound_code_val code msg' := by
  apply causal_code_val_unique F net sess code (msg + msg')
  · exact linear_code_supports_rate_cut_bound_code_val_recurrence code (msg + msg')
  · intro m
    rw [Pi.add_apply, linear_code_supports_rate_cut_bound_code_val_recurrence code msg m,
      linear_code_supports_rate_cut_bound_code_val_recurrence code msg' m]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    abel

theorem linear_code_supports_rate_cut_bound_code_val_smul
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    {F : Type} [Field F] {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (c : F) (msg : K → Fin code.L → F) :
    linear_code_supports_rate_cut_bound_code_val code (c • msg) =
      c • linear_code_supports_rate_cut_bound_code_val code msg := by
  apply causal_code_val_unique F net sess code (c • msg)
  · exact linear_code_supports_rate_cut_bound_code_val_recurrence code (c • msg)
  · intro m
    rw [Pi.smul_apply, linear_code_supports_rate_cut_bound_code_val_recurrence code msg m]
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro j _
      ring
    · apply Finset.sum_congr rfl; intro m' _
      ring

abbrev linear_code_supports_rate_cut_bound_kout {V K : Type} (sess : UnicastSessions V K) (S : Finset V) :=
  {k : K // sess.src k ∈ S ∧ sess.tgt k ∉ S}

abbrev linear_code_supports_rate_cut_bound_mout {V K F : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [Field F]
    {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) :=
  {m : Fin code.M // code.snd m ∈ S ∧ code.rcv m ∉ S}

noncomputable def linear_code_supports_rate_cut_bound_extend_msg {V K F : Type} [Zero F] [DecidableEq V]
    {sess : UnicastSessions V K} (L : ℕ) (S : Finset V)
    (f : linear_code_supports_rate_cut_bound_kout sess S → Fin L → F) : K → Fin L → F :=
  fun k j => if h : sess.src k ∈ S ∧ sess.tgt k ∉ S then f ⟨k, h⟩ j else 0

noncomputable def linear_code_supports_rate_cut_bound_cut_map {V K F : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [Field F]
    {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) :
    (linear_code_supports_rate_cut_bound_kout sess S → Fin code.L → F) →ₗ[F]
      (linear_code_supports_rate_cut_bound_mout code S → F) where
  toFun f m := linear_code_supports_rate_cut_bound_code_val code (linear_code_supports_rate_cut_bound_extend_msg code.L S f) m.1
  map_add' f g := by
    ext m
    have h_ext : linear_code_supports_rate_cut_bound_extend_msg code.L S (f + g) =
      linear_code_supports_rate_cut_bound_extend_msg code.L S f + linear_code_supports_rate_cut_bound_extend_msg code.L S g := by
      ext k j
      simp only [linear_code_supports_rate_cut_bound_extend_msg, Pi.add_apply]
      split_ifs <;> simp
    rw [h_ext, linear_code_supports_rate_cut_bound_code_val_add]
    rfl
  map_smul' c f := by
    ext m
    have h_ext : linear_code_supports_rate_cut_bound_extend_msg code.L S (c • f) =
      c • linear_code_supports_rate_cut_bound_extend_msg code.L S f := by
      ext k j
      simp only [linear_code_supports_rate_cut_bound_extend_msg, Pi.smul_apply]
      split_ifs <;> simp
    rw [h_ext, linear_code_supports_rate_cut_bound_code_val_smul]
    rfl

theorem linear_code_supports_rate_cut_bound_cut_map_injective {V K F : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [Field F]
    {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) :
    Function.Injective (linear_code_supports_rate_cut_bound_cut_map code S) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h_mzero : ∀ m : linear_code_supports_rate_cut_bound_mout code S,
      linear_code_supports_rate_cut_bound_code_val code (linear_code_supports_rate_cut_bound_extend_msg code.L S f) m.1 = 0 := by
    intro m
    exact congr_fun hf m
  have h_outside := causal_code_vals_zero_outside F net sess code S
    (linear_code_supports_rate_cut_bound_extend_msg code.L S f)
    (linear_code_supports_rate_cut_bound_code_val code (linear_code_supports_rate_cut_bound_extend_msg code.L S f))
    (linear_code_supports_rate_cut_bound_code_val_recurrence code (linear_code_supports_rate_cut_bound_extend_msg code.L S f))
    (by
      intro k j hk
      dsimp [linear_code_supports_rate_cut_bound_extend_msg]
      split_ifs with h
      · exact False.elim (hk h.1)
      · rfl)
    (by
      intro m hsnd hrcv
      exact h_mzero ⟨m, hsnd, hrcv⟩)
  ext ⟨k, hk⟩ j
  have h_dec := linear_code_supports_rate_cut_bound_code_val_decode code
    (linear_code_supports_rate_cut_bound_extend_msg code.L S f) k j
  dsimp [linear_code_supports_rate_cut_bound_extend_msg] at h_dec
  split_ifs at h_dec
  rw [h_dec]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hγ : code.γ k j m = 0
  · rw [hγ, zero_mul]
  · have h_tgt := code.dec_local k j m hγ
    have h_rcv_not : code.rcv m ∉ S := by
      rw [h_tgt]
      exact hk.2
    have h_val_zero := h_outside m h_rcv_not
    rw [h_val_zero, mul_zero]

theorem linear_code_supports_rate_cut_bound_cut_card_le {V K F : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [Field F]
    {net : CapacitatedNetwork V} {sess : UnicastSessions V K}
    (code : CausalLinearNetworkCode V K F net sess) (S : Finset V) :
    Fintype.card (linear_code_supports_rate_cut_bound_kout sess S) * code.L ≤
      Fintype.card (linear_code_supports_rate_cut_bound_mout code S) := by
  have hinj := linear_code_supports_rate_cut_bound_cut_map_injective code S
  have hrank := LinearMap.finrank_le_finrank_of_injective hinj
  have e : (linear_code_supports_rate_cut_bound_kout sess S → Fin code.L → F) ≃ₗ[F]
      (linear_code_supports_rate_cut_bound_kout sess S × Fin code.L → F) :=
    (LinearEquiv.curry F F (linear_code_supports_rate_cut_bound_kout sess S) (Fin code.L)).symm
  rw [LinearEquiv.finrank_eq e] at hrank
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  rw [Fintype.card_prod, Fintype.card_fin] at hrank
  exact hrank

/-- Cut-set bound: the rate of a linear network code is at most capacity over crossing sessions on every cut. -/
theorem linear_code_supports_rate_cut_bound
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r : ℝ}
    (h : LinearCodeSupportsRate F net sess r) (S : Finset V) :
    r * (cutSeparation sess S : ℝ) ≤ cutCapacity net S := by
  rcases h with ⟨code, hr⟩
  have h_le_S := linear_code_supports_rate_cut_bound_cut_card_le code S
  have h_le_Sc := linear_code_supports_rate_cut_bound_cut_card_le code Sᶜ
  have h_sum_le : (Fintype.card (linear_code_supports_rate_cut_bound_kout sess S) +
      Fintype.card (linear_code_supports_rate_cut_bound_kout sess Sᶜ)) * code.L ≤
    Fintype.card (linear_code_supports_rate_cut_bound_mout code S) +
      Fintype.card (linear_code_supports_rate_cut_bound_mout code Sᶜ) := by
    calc
      _ = Fintype.card (linear_code_supports_rate_cut_bound_kout sess S) * code.L +
          Fintype.card (linear_code_supports_rate_cut_bound_kout sess Sᶜ) * code.L := by ring
      _ ≤ _ := add_le_add h_le_S h_le_Sc
  have h_k_eq : cutSeparation sess S =
      Fintype.card (linear_code_supports_rate_cut_bound_kout sess S) +
      Fintype.card (linear_code_supports_rate_cut_bound_kout sess Sᶜ) := by
    dsimp [cutSeparation]
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h_eq : (Finset.univ.filter (fun k => (sess.src k ∈ S) ≠ (sess.tgt k ∈ S))) =
      (Finset.univ.filter (fun k => sess.src k ∈ S ∧ sess.tgt k ∉ S)) ∪
      (Finset.univ.filter (fun k => sess.src k ∈ Sᶜ ∧ sess.tgt k ∉ Sᶜ)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_compl]
      tauto
    rw [h_eq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    simp only [Finset.mem_compl] at h2
    exact h2.1 h1.1
  have h_m_eq : (Finset.univ.filter (fun m : Fin code.M => (code.snd m ∈ S) ≠ (code.rcv m ∈ S))).card =
      Fintype.card (linear_code_supports_rate_cut_bound_mout code S) +
      Fintype.card (linear_code_supports_rate_cut_bound_mout code Sᶜ) := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h_eq : (Finset.univ.filter (fun m : Fin code.M => (code.snd m ∈ S) ≠ (code.rcv m ∈ S))) =
      (Finset.univ.filter (fun m => code.snd m ∈ S ∧ code.rcv m ∉ S)) ∪
      (Finset.univ.filter (fun m => code.snd m ∈ Sᶜ ∧ code.rcv m ∉ Sᶜ)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_compl]
      tauto
    rw [h_eq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_filter]
    intro m _ h1 h2
    simp only [Finset.mem_compl] at h2
    exact h2.1 h1.1
  rw [← h_k_eq] at h_sum_le
  rw [← h_m_eq] at h_sum_le
  have h_trans := code_transmissions_cross_cut_le F net sess code S
  have h_sep_L_le : (cutSeparation sess S : ℝ) * (code.L : ℝ) ≤ (code.T : ℝ) * cutCapacity net S := by
    have h_nat : (cutSeparation sess S : ℝ) * (code.L : ℝ) ≤
      ↑(Finset.univ.filter (fun m : Fin code.M => (code.snd m ∈ S) ≠ (code.rcv m ∈ S))).card := by
      exact_mod_cast h_sum_le
    exact le_trans h_nat h_trans
  have hT_pos : 0 < (code.T : ℝ) := Nat.cast_pos.mpr code.hT
  have hsep_nonneg : 0 ≤ (cutSeparation sess S : ℝ) := Nat.cast_nonneg (cutSeparation sess S)
  have h1 : r * (cutSeparation sess S : ℝ) ≤ ((code.L : ℝ) / (code.T : ℝ)) * (cutSeparation sess S : ℝ) :=
    mul_le_mul_of_nonneg_right hr hsep_nonneg
  have h2 : ((code.L : ℝ) / (code.T : ℝ)) * (cutSeparation sess S : ℝ) =
    ((cutSeparation sess S : ℝ) * (code.L : ℝ)) / (code.T : ℝ) := by ring
  rw [h2] at h1
  have h3 : ((cutSeparation sess S : ℝ) * (code.L : ℝ)) / (code.T : ℝ) ≤ cutCapacity net S := by
    exact (div_le_iff₀ hT_pos).mpr (by linarith)
  linarith
