import AFTD.Prelude
import AFTD.Kb.Tcs.Op309ConnectedTriangleFreeClassCycleBudget

/-!
# op309_girth34_connected_class_cycle_budget

Topic: graphs   Node: e047fcdb2eef

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

Connected class-support graphs of girth at least 34 and maximum degree three, with total cycle rank t, degree-three budget 2s, and edge budget k, satisfy 34t ≤ 34s+k.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem in1099_cycle_budget_34
    {ι : Type*} [Fintype ι] (cyc branch edges : ι → ℕ) (s k : ℕ)
    (hlocal : ∀ i, 2 * cyc i ≤ branch i + 2 * (if cyc i = 0 then 0 else 1))
    (hsize : ∀ i, 34 * (if cyc i = 0 then 0 else 1) ≤ edges i)
    (hbranch : ∑ i, branch i ≤ 2*s)
    (hedges : ∑ i, edges i ≤ k) :
    34 * (∑ i, cyc i) ≤ 34*s + k := by
  classical
  have h₁ : ∑ i, (2 * cyc i) ≤ ∑ i, (branch i + 2 * (if cyc i = 0 then 0 else 1)) :=
    Finset.sum_le_sum fun i _ => hlocal i
  have h₂ : ∑ i, (34 * (if cyc i = 0 then 0 else 1)) ≤ ∑ i, edges i :=
    Finset.sum_le_sum fun i _ => hsize i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h₁ h₂
  omega

theorem in1099_cyclic_support_has_34_edges {V : Type*}
    [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) (hgirth : (34 : ℕ∞) ≤ H.egirth)
    (hcyc : 0 < H.edgeFinset.card + 1 - Fintype.card V) :
    34 ≤ H.edgeFinset.card := by
  classical
  have hnot : ¬ H.IsAcyclic := by
    intro hac
    have ht : H.IsTree := ⟨hconn,hac⟩
    have hcard := ht.card_edgeFinset
    omega
  obtain ⟨v,w,hw,heq⟩ := H.exists_egirth_eq_length.mpr hnot
  have hlen : 34 ≤ w.length := by
    have hle : (34 : ℕ∞) ≤ (w.length : ℕ∞) := hgirth.trans_eq heq
    exact_mod_cast hle
  exact hlen.trans hw.isTrail.length_le_card_edgeFinset

theorem op309_girth34_connected_class_cycle_budget
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (H : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (H i).Adj]
    (s k : ℕ)
    (hconn : ∀ i, (H i).Connected)
    (hgirth : ∀ i, (34 : ℕ∞) ≤ (H i).egirth)
    (hdeg : ∀ i v, (H i).degree v ≤ 3)
    (hbranch : (∑ i, (Finset.univ.filter fun v => (H i).degree v = 3).card) ≤ 2*s)
    (hedges : (∑ i, (H i).edgeFinset.card) ≤ k) :
    34 * (∑ i, ((H i).edgeFinset.card + 1 - Fintype.card (V i))) ≤ 34*s + k := by
  let cyc : ι → ℕ := fun i => (H i).edgeFinset.card + 1 - Fintype.card (V i)
  let branch : ι → ℕ := fun i => (Finset.univ.filter fun v => (H i).degree v = 3).card
  let edges : ι → ℕ := fun i => (H i).edgeFinset.card
  apply in1099_cycle_budget_34 cyc branch edges s k
  · intro i
    exact in1099_branch_cycle_bound (H i) (hdeg i)
  · intro i
    dsimp [cyc,edges]
    split
    · simp
    · rename_i hn
      simp only [if_neg hn, mul_one]
      exact in1099_cyclic_support_has_34_edges (H i) (hconn i) (hgirth i) (Nat.pos_of_ne_zero hn)
  · exact hbranch
  · exact hedges
