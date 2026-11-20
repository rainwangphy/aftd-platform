import AFTD.Prelude
import AFTD.Kb.Tcs.Op309ConnectedTriangleFreeClassCycleBudget
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op309_girth34_class_support_density

Topic: graphs   Node: ec30a7b26fe5

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

For connected girth-at-least-34 class-support graphs with the displayed degree, endpoint, branch, host-edge and peeling counts, the ambient vertex count is at most 108 times the uncovered count.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem in1099density_cycle_budget_34
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

theorem in1099density_cyclic_support_has_34_edges {V : Type*}
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

theorem in1099density_connected_girth34_class_cycle_budget
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
  apply in1099density_cycle_budget_34 cyc branch edges s k
  · intro i
    exact in1099_branch_cycle_bound (H i) (hdeg i)
  · intro i
    dsimp [cyc,edges]
    split
    · simp
    · rename_i hn
      simp only [if_neg hn, mul_one]
      exact in1099density_cyclic_support_has_34_edges (H i) (hconn i) (hgirth i) (Nat.pos_of_ne_zero hn)
  · exact hbranch
  · exact hedges


theorem in1099density_class_graph_cycle_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, 1 ≤ H.degree v ∧ H.degree v ≤ 3)
    (hconn : H.Connected) :
    2 * (H.edgeFinset.card + 1 - Fintype.card V) +
      (Finset.univ.filter fun v => H.degree v = 1).card =
      2 + (Finset.univ.filter fun v => H.degree v = 3).card := by
  classical
  have hs : (∑ v, (H.degree v + if H.degree v = 1 then 1 else 0)) =
      ∑ v, (2 + if H.degree v = 3 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hd := hdeg v
    split_ifs <;> omega
  have hs' : (∑ v, H.degree v) + (Finset.univ.filter fun v => H.degree v = 1).card =
      2 * Fintype.card V + (Finset.univ.filter fun v => H.degree v = 3).card := by
    simpa [Finset.sum_add_distrib, ← Finset.sum_filter, Nat.mul_comm] using hs
  have hh := H.sum_degrees_eq_twice_card_edges
  have hcard : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, ← H.edgeFinset_card] using hconn.card_vert_le_card_edgeSet_add_one
  omega


theorem in1099density_class_count_identity
    {ι : Type*} [Fintype ι] (cyc ends branch : ι → Nat)
    (p s z u q : Nat)
    (hlocal : ∀ i, 2 * cyc i + ends i = 2 + branch i)
    (hends : (∑ i, ends i) = p + 2*z + 3*u)
    (hbranch : (∑ i, branch i) = 2*s)
    (hcount : Fintype.card ι = q) :
    2*q + 2*s = p + 2*z + 3*u + 2 * (∑ i, cyc i) := by
  classical
  have hsum : (∑ i, (2 * cyc i + ends i)) = ∑ i, (2 + branch i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hlocal i
  have hmul : (∑ i, 2 * cyc i) = 2 * (∑ i, cyc i) := by rw [Finset.mul_sum]
  have hconst : (∑ _ : ι, (2 : Nat)) = 2 * Fintype.card ι := by simp [Nat.mul_comm]
  simp only [Finset.sum_add_distrib, hmul, hconst] at hsum
  rw [hends,hbranch,hcount] at hsum
  omega


theorem in1099density_girth34_full_support_arithmetic
    (n p s z u q t k : Nat)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hclass : 2*q + 2*s = p + 2*z + 3*u + 2*t)
    (hpeel : 3*p + s + 6*z + 3*u ≤ 5*q)
    (hhost : 2*k = 5*p + 6*s + 6*z + 3*u)
    (hcycles : 34*t ≤ 34*s + k) :
    9*p + 38*s + 38*z ≤ 321*u ∧ n ≤ 108*u := by
  constructor <;> nlinarith

theorem op309_girth34_class_support_density
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (H : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (H i).Adj]
    (n p s z u q k : Nat)
    (hconn : ∀ i, (H i).Connected)
    (hgirth : ∀ i, (34 : ℕ∞) ≤ (H i).egirth)
    (hdeg : ∀ i v, 1 ≤ (H i).degree v ∧ (H i).degree v ≤ 3)
    (hends : (∑ i, (Finset.univ.filter fun v => (H i).degree v = 1).card) = p + 2*z + 3*u)
    (hbranch : (∑ i, (Finset.univ.filter fun v => (H i).degree v = 3).card) = 2*s)
    (hcount : Fintype.card ι = q)
    (hedges : (∑ i, (H i).edgeFinset.card) ≤ k)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hpeel : 3*p + s + 6*z + 3*u ≤ 5*q)
    (hhost : 2*k = 5*p + 6*s + 6*z + 3*u) : n ≤ 108*u := by
  let cyc : ι → Nat := fun i => (H i).edgeFinset.card + 1 - Fintype.card (V i)
  let ends : ι → Nat := fun i => (Finset.univ.filter fun v => (H i).degree v = 1).card
  let branch : ι → Nat := fun i => (Finset.univ.filter fun v => (H i).degree v = 3).card
  have hlocal : ∀ i, 2*cyc i + ends i = 2 + branch i := by
    intro i
    exact in1099density_class_graph_cycle_identity (H i) (hdeg i) (hconn i)
  have hclass := in1099density_class_count_identity cyc ends branch p s z u q hlocal hends hbranch hcount
  have hcyc := in1099density_connected_girth34_class_cycle_budget V H s k hconn hgirth
    (fun i v => (hdeg i v).2) (le_of_eq hbranch) hedges
  exact (in1099density_girth34_full_support_arithmetic n p s z u q (∑ i,cyc i) k
    hvertices hclass hpeel hhost hcyc).2
