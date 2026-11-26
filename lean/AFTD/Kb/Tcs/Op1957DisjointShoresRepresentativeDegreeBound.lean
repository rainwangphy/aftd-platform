import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957DisjointShoresDefectBudget

/-!
# op1957_disjoint_shores_representative_degree_bound

Topic: graphs   Node: 5055d65079ef

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Disjoint shores representative degree bound.
-/

set_option maxHeartbeats 2000000

theorem op1957_disjoint_shores_representative_degree_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Finset I) (F : I → Finset V) (E T : Finset V) (j : I) (v : V)
    (hj : j ∈ J) (hv : v ∈ F j)
    (hdis : ∀ i ∈ J, ∀ l ∈ J, i ≠ l → Disjoint (F i) (F l))
    (hdisE : ∀ i ∈ J, Disjoint (F i) E)
    (hanti : ∀ i ∈ J, i ≠ j → ∀ w ∈ F i, ¬ G.Adj v w)
    (hantiE : ∀ w ∈ E, ¬ G.Adj v w)
    (hvT : v ∉ T) (hforbid : ∀ w ∈ T, ¬ G.Adj v w)
    (L s : ℕ) (hs : 3 ≤ s)
    (hsize : Fintype.card V = T.card+(L+s-1)+1)
    (hdegree : L+2 ≤ (G.neighborFinset v).card) :
    (∑ i ∈ J.erase j, (F i \ T).card) + (E \ T).card + 3 ≤ s := by
  have hd : L+s-1 ≤ (G.neighborFinset v).card+(s-3) := by omega
  have hh := op1957_disjoint_shores_defect_budget G J F E T j v hj hv hdis hdisE hanti hantiE
    hvT hforbid (L+s-1) (s-3) hsize hd
  omega
