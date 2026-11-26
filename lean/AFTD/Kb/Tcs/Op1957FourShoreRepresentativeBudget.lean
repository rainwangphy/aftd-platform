import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957DisjointShoresRepresentativeDegreeBound
import AFTD.Kb.Tcs.Op1957FourShoreChooseNonendpointRepresentative
import AFTD.Kb.Tcs.Op1957FourShoreNonendpointAnticomplete

/-!
# op1957_four_shore_representative_budget

Topic: graphs   Node: 0b5e8d1b199a

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore representative budget.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_representative_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F B : Fin 4 → Finset V) (E : Finset V) (x y : V)
    (hFdis : ∀ i l : Fin 4, i ≠ l → Disjoint (F i) (F l))
    (hEdis : ∀ i : Fin 4, Disjoint (F i) E)
    (hBdis : ∀ i l : Fin 4, i ≠ l → Disjoint (B i) (B l))
    (hx : x ∈ B 0) (hy : y ∈ B 2)
    (hcross : ∀ i l : Fin 4, i ≠ l → ∀ a ∈ F i, ∀ b ∈ F l, G.Adj a b →
      (i=0 ∧ l=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ l=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i : Fin 4, ∀ a ∈ F i, ∀ w ∈ E, ¬ G.Adj a w)
    (j b forbidden : Fin 4) (hbf : b ≠ forbidden)
    (hforbid : ∀ a ∈ B b, ∀ w ∈ B forbidden, ¬ G.Adj a w)
    (L : ℕ) (hs : 3 ≤ (B b).card)
    (hsize : Fintype.card V = (B forbidden).card+(L+(B b).card-1)+1)
    (hdegree : ∀ v, L+2 ≤ (G.neighborFinset v).card)
    (hcount : (if (j=0 ∧ b=0) ∨ (j=1 ∧ b=2) then 2 else 1) ≤ (F j ∩ B b).card) :
    (∑ i ∈ (Finset.univ : Finset (Fin 4)).erase j, (F i \ B forbidden).card) +
      (E \ B forbidden).card + 3 ≤ (B b).card := by
  classical
  obtain ⟨v,hvF,hvB,hnotx,hnoty⟩ :=
    op1957_four_shore_choose_nonendpoint_representative F B x y hBdis hx hy j b hcount
  have hvT : v ∉ B forbidden := fun h => Finset.disjoint_left.mp (hBdis b forbidden hbf) hvB h
  have hanti := op1957_four_shore_nonendpoint_anticomplete G F x y hcross j v hvF hnotx hnoty
  apply op1957_disjoint_shores_representative_degree_bound G Finset.univ F E (B forbidden) j v
    (Finset.mem_univ j) hvF
    (by intro i _ l _ hil; exact hFdis i l hil)
    (by intro i _; exact hEdis i)
    (by intro i _ hij; exact hanti i hij)
    (hEanti j v hvF) hvT (hforbid v hvB) L (B b).card hs hsize (hdegree v)
