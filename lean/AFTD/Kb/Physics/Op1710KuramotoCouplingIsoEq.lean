import AFTD.Prelude
import AFTD.Kb.Physics.KuramotoCriticalCoupling
import AFTD.Kb.Tcs.G

/-!
# op_1710_kuramoto_coupling_iso_eq

Topic: classical_mechanics   Node: e00af99e354d

Provenance: helper lemma. folklore

For any two isomorphic graphs T and T' on a finite vertex set V, any probability measure μ on ℝ, and any threshold s, the probability that the Kuramoto critical coupling is at most s is identical for T and T'.
-/

def op_1710_deleteEdgesIso {V : Type*} (T T' : SimpleGraph V) (e : T ≃g T') (u v : V) :
    T.deleteEdges {s(u, v)} ≃g T'.deleteEdges {s(e u, e v)} where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change (T'.deleteEdges {s(e u, e v)}).Adj (e x) (e y) ↔ (T.deleteEdges {s(u, v)}).Adj x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    rw [SimpleGraph.Iso.map_adj_iff e]
    have : s(e x, e y) = s(e u, e v) ↔ s(x, y) = s(u, v) := by
      rw [← Sym2.map_mk, ← Sym2.map_mk]
      exact (Sym2.map.injective e.injective).eq_iff
    exact and_congr_right_iff.mpr fun _ => not_congr this

theorem op_1710_reachable_deleteEdges_iff {V : Type*} (T T' : SimpleGraph V) (e : T ≃g T') (u v w : V) :
    (T'.deleteEdges {s(e u, e v)}).Reachable (e u) (e w) ↔ (T.deleteEdges {s(u, v)}).Reachable u w :=
  (op_1710_deleteEdgesIso T T' e u v).reachable_iff (u := u) (v := w)

open scoped Classical in
lemma op_1710_inner_sum_eq {V : Type*} [Fintype V] (T T' : SimpleGraph V) (e : T ≃g T') (ω : V → ℝ) (m : ℝ) (u v : V) :
    (∑ w : V, if (T'.deleteEdges {s(e u, e v)}).Reachable (e u) w then (ω (e.symm w) - m) else 0) =
    (∑ w : V, if (T.deleteEdges {s(u, v)}).Reachable u w then (ω w - m) else 0) := by
  have h := (e.toEquiv.sum_comp (fun w => if (T'.deleteEdges {s(e u, e v)}).Reachable (e u) w then (ω (e.symm w) - m) else 0)).symm
  rw [h]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : (e.toEquiv w : V) = e w := rfl
  simp only [h1, op_1710_reachable_deleteEdges_iff, RelIso.symm_apply_apply]

open scoped Classical in
lemma op_1710_kuramoto_coupling_comp_symm {V : Type*} [Fintype V]
    (T T' : SimpleGraph V) (e : T ≃g T') (ω : V → ℝ) :
    kuramoto_critical_coupling T' (fun v => ω (e.symm v)) = kuramoto_critical_coupling T ω := by
  unfold kuramoto_critical_coupling
  dsimp only
  have hmean_sum : (∑ v : V, ω (e.symm v)) = ∑ v : V, ω v := by
    have : (fun v => ω (e.symm v)) = (fun v => ω (e.symm.toEquiv v)) := rfl
    rw [this, e.symm.toEquiv.sum_comp]
  rw [hmean_sum]
  rw [← e.toEquiv.iSup_comp]
  refine iSup_congr fun u => ?_
  rw [← e.toEquiv.iSup_comp]
  refine iSup_congr fun v => ?_
  have hadj : T'.Adj (e.toEquiv u) (e.toEquiv v) ↔ T.Adj u v := by
    change T'.Adj (e u) (e v) ↔ T.Adj u v
    exact SimpleGraph.Iso.map_adj_iff e
  refine iSup_congr_Prop hadj fun h => ?_
  congr 1
  set m := (∑ v, ω v) / (Fintype.card V : ℝ)
  exact op_1710_inner_sum_eq T T' e ω m u v

/-- Isomorphic trees have identical Kuramoto critical coupling cumulative distributions under exchangeable i.i.d. frequencies. -/
theorem op_1710_kuramoto_coupling_iso_eq {V : Type*} [Fintype V]
    (T T' : SimpleGraph V) (e : T ≃g T')
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (s : ℝ) :
    MeasureTheory.Measure.pi (fun (_ : V) ↦ μ) { ω | kuramoto_critical_coupling T ω ≤ s } =
    MeasureTheory.Measure.pi (fun (_ : V) ↦ μ) { ω | kuramoto_critical_coupling T' ω ≤ s } := by
  let F := MeasurableEquiv.piCongrLeft (fun _ : V ↦ ℝ) e.toEquiv
  have hmp : MeasureTheory.MeasurePreserving F
      (MeasureTheory.Measure.pi fun _ ↦ μ) (MeasureTheory.Measure.pi fun _ ↦ μ) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ ↦ μ) e.toEquiv
  have hpre := hmp.measure_preimage_equiv { ω | kuramoto_critical_coupling T' ω ≤ s }
  rw [← hpre]
  congr 1
  ext ω
  have hF : F ω = fun v ↦ ω (e.symm v) := by
    ext v
    simp [F, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rfl
  change kuramoto_critical_coupling T ω ≤ s ↔ kuramoto_critical_coupling T' (F ω) ≤ s
  rw [hF, op_1710_kuramoto_coupling_comp_symm T T' e ω]
