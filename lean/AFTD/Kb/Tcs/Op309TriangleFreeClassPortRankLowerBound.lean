import AFTD.Prelude

/-!
# op309_triangle_free_class_port_rank_lower_bound

Topic: graphs   Node: 7fe3e2c9a0d0

Provenance: helper lemma. OP-309 high-girth port-class incidence route, IN-1099.

Given the explicit cubic count and incidence-rank identities and connected triangle-free class supports of maximum degree three with the stated edge and branching budgets, the incidence rank is at least one plus one sixteenth of the graph order.
-/

set_option maxHeartbeats 0

theorem in1099_cond_cycle_budget
    {ι : Type*} [Fintype ι] (cyc branch edges : ι → ℕ) (s k : ℕ)
    (hlocal : ∀ i, 2 * cyc i ≤ branch i + 2 * (if cyc i = 0 then 0 else 1))
    (hsize : ∀ i, 4 * (if cyc i = 0 then 0 else 1) ≤ edges i)
    (hbranch : ∑ i, branch i ≤ 2*s)
    (hedges : ∑ i, edges i ≤ k) :
    ∑ i, cyc i ≤ s + k/4 := by
  classical
  have h₁ : ∑ i, (2 * cyc i) ≤ ∑ i, (branch i + 2 * (if cyc i = 0 then 0 else 1)) :=
    Finset.sum_le_sum fun i _ => hlocal i
  have h₂ : ∑ i, (4 * (if cyc i = 0 then 0 else 1)) ≤ ∑ i, edges i :=
    Finset.sum_le_sum fun i _ => hsize i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h₁ h₂
  omega


theorem in1099_cond_branch_cycle_bound {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 3) :
    let rank := H.edgeFinset.card + 1 - Fintype.card V
    2 * rank ≤ (Finset.univ.filter fun v => H.degree v = 3).card +
      2 * (if rank = 0 then 0 else 1) := by
  classical
  have hsum : (∑ v, H.degree v) ≤
      2 * Fintype.card V + (Finset.univ.filter fun v => H.degree v = 3).card := by
    calc
      (∑ v, H.degree v) ≤ ∑ v, (2 + if H.degree v = 3 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        have hd := hdeg v
        split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]
  have hhand := H.sum_degrees_eq_twice_card_edges
  dsimp only
  split <;> omega


theorem in1099_cond_cyclic_support_has_four_edges {V : Type*}
    [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) (hgirth : (4 : ℕ∞) ≤ H.egirth)
    (hcyc : 0 < H.edgeFinset.card + 1 - Fintype.card V) :
    4 ≤ H.edgeFinset.card := by
  classical
  have hnot : ¬ H.IsAcyclic := by
    intro hac
    have ht : H.IsTree := ⟨hconn,hac⟩
    have hcard := ht.card_edgeFinset
    omega
  obtain ⟨v,w,hw,heq⟩ := H.exists_egirth_eq_length.mpr hnot
  have hlen : 4 ≤ w.length := by
    have hle : (4 : ℕ∞) ≤ (w.length : ℕ∞) := hgirth.trans_eq heq
    exact_mod_cast hle
  exact hlen.trans hw.isTrail.length_le_card_edgeFinset


theorem in1099_cond_connected_class_cycle_budget
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (H : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (H i).Adj]
    (s k : ℕ)
    (hconn : ∀ i, (H i).Connected)
    (hgirth : ∀ i, (4 : ℕ∞) ≤ (H i).egirth)
    (hdeg : ∀ i v, (H i).degree v ≤ 3)
    (hbranch : (∑ i, (Finset.univ.filter fun v => (H i).degree v = 3).card) ≤ 2*s)
    (hedges : (∑ i, (H i).edgeFinset.card) ≤ k) :
    (∑ i, ((H i).edgeFinset.card + 1 - Fintype.card (V i))) ≤ s + k/4 := by
  let cyc : ι → ℕ := fun i => (H i).edgeFinset.card + 1 - Fintype.card (V i)
  let branch : ι → ℕ := fun i => (Finset.univ.filter fun v => (H i).degree v = 3).card
  let edges : ι → ℕ := fun i => (H i).edgeFinset.card
  apply in1099_cond_cycle_budget cyc branch edges s k
  · intro i
    exact in1099_cond_branch_cycle_bound (H i) (hdeg i)
  · intro i
    dsimp [cyc,edges]
    split
    · simp
    · rename_i hn
      simp only [if_neg hn, mul_one]
      exact in1099_cond_cyclic_support_has_four_edges (H i) (hconn i) (hgirth i) (Nat.pos_of_ne_zero hn)
  · exact hbranch
  · exact hedges


theorem in1099_cond_rank_triangle_free_arithmetic
    (n m r k p s z u cyclic rank : ℕ)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hselected : r = 2*p + 3*s + 3*z)
    (hcubic : 2*m = 3*n)
    (heven : n % 2 = 0)
    (hhost : k + r + 3*u = m)
    (hrank : rank + cyclic = n/2 + 1)
    (hcycles : cyclic ≤ s + k/4) :
    8 + 7*p + 2*s + 10*z + 7*u ≤ 8*rank ∧
      16 + n ≤ 16*rank := by
  constructor <;> omega

theorem op309_triangle_free_class_port_rank_lower_bound{ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (H : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (H i).Adj]
    (n m r k p s z u rank : ℕ)
    (hvertices : n = 3*p + 4*s + 4*z + u)
    (hselected : r = 2*p + 3*s + 3*z)
    (hcubic : 2*m = 3*n) (heven : n % 2 = 0)
    (hhost : k + r + 3*u = m)
    (hrank : rank + (∑ i, ((H i).edgeFinset.card + 1 - Fintype.card (V i))) = n/2 + 1)
    (hconn : ∀ i, (H i).Connected)
    (hgirth : ∀ i, (4 : ℕ∞) ≤ (H i).egirth)
    (hdeg : ∀ i v, (H i).degree v ≤ 3)
    (hbranch : (∑ i, (Finset.univ.filter fun v => (H i).degree v = 3).card) ≤ 2*s)
    (hedges : (∑ i, (H i).edgeFinset.card) ≤ k) :
    16 + n ≤ 16*rank := by
  have hb := in1099_cond_connected_class_cycle_budget V H s k hconn hgirth hdeg hbranch hedges
  exact (in1099_cond_rank_triangle_free_arithmetic n m r k p s z u _ rank
    hvertices hselected hcubic heven hhost hrank hb).2
