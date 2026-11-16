import AFTD.Prelude
import AFTD.Kb.Tcs.IsTotalEdgeIrregularLabeling
import AFTD.Kb.Tcs.TotalEdgeIrregularityStrength

/-!
# cubic_total_edge_irregularity_strength_lower_bound

Topic: graphs   Node: 45d9c4c186ce

Provenance: helper lemma. arXiv:2611.16338, Section 1, equation (1)

Every finite simple graph G on a finite type V that is regular of degree 3 satisfies Fintype.card V / 2 + 1 ≤ total_edge_irregularity_strength G.
-/

open scoped Classical in
/-- The total edge irregularity strength of a finite simple cubic graph is at least |V| / 2 + 1. -/
theorem cubic_total_edge_irregularity_strength_lower_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hreg : G.IsRegularOfDegree 3) :
    Fintype.card V / 2 + 1 ≤ total_edge_irregularity_strength G := by
  dsimp [total_edge_irregularity_strength]
  have hnonempty : {s : ℕ | 0 < s ∧ ∃ (φ : V → ℕ) (ψ : G.edgeSet → ℕ), is_total_edge_irregular_labeling G s φ ψ}.Nonempty := by
    let e := Fintype.equivFin G.edgeSet
    let s := max 1 G.edgeFinset.card
    have hs : 0 < s := by omega
    refine ⟨s, hs, fun _ => 1, fun x => (e x).val + 1, ?_⟩
    dsimp [is_total_edge_irregular_labeling]
    refine ⟨?_, ?_, ?_⟩
    · intro v
      omega
    · intro x
      have hlt := (e x).isLt
      have hc : Fintype.card G.edgeSet = G.edgeFinset.card := SimpleGraph.card_edgeSet
      omega
    · intro x y h
      have h1 : Sym2.lift ⟨fun u v => (1 : ℕ) + 1, fun _ _ => rfl⟩ x.val = 2 := by
        induction x.val using Sym2.inductionOn
        rfl
      have h2 : Sym2.lift ⟨fun u v => (1 : ℕ) + 1, fun _ _ => rfl⟩ y.val = 2 := by
        induction y.val using Sym2.inductionOn
        rfl
      rw [h1, h2] at h
      have : (e x).val = (e y).val := by omega
      have : e x = e y := Fin.ext this
      exact e.injective this
  apply le_csInf hnonempty
  intro s hs
  rcases hs with ⟨hs_pos, φ, ψ, hlabel⟩
  rcases hlabel with ⟨hφ, hψ, hirr⟩
  let w : G.edgeSet → ℕ := fun e =>
    Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val + ψ e
  have hw_inj : Function.Injective w := hirr
  have hw_mem : ∀ e : G.edgeSet, w e ∈ Finset.Icc 3 (3 * s) := by
    intro e
    rw [Finset.mem_Icc]
    have hψe := hψ e
    have hφe : 2 ≤ Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val ∧
        Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val ≤ 2 * s := by
      induction e.val using Sym2.inductionOn with
      | hf u v =>
        dsimp
        have hu := hφ u
        have hv := hφ v
        omega
    dsimp [w]
    omega
  have himage : Finset.univ.image w ⊆ Finset.Icc 3 (3 * s) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨e, -, rfl⟩
    exact hw_mem e
  have hcard_le := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ hw_inj, Finset.card_univ] at hcard_le
  rw [Nat.card_Icc] at hcard_le
  have hc : Fintype.card G.edgeSet = G.edgeFinset.card := SimpleGraph.card_edgeSet
  have h1 : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h2 : ∑ v : V, G.degree v = ∑ v : V, 3 := by
    apply Finset.sum_congr rfl
    intro v _
    exact hreg v
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  omega
