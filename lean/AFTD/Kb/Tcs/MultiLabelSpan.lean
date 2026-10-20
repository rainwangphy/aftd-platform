import AFTD.Prelude

/-!
# multi_label_span

Topic: graphs   Node: 18e3dc3a9ab7

Provenance: formalization of a published result. Source: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Sec. 1 (span)

The span of a multi-labeling: the largest label used minus the smallest (written as the largest difference b - a over all pairs of labels).
-/

/-- The span of a multi-labeling: the largest label used minus the smallest (written as the largest difference b - a over all pairs of labels). -/
def multi_label_span {V : Type*} [Fintype V] (f : V → Finset ℕ) : ℕ :=
  Finset.univ.sup fun x => Finset.univ.sup fun y => (f x).sup fun a => (f y).sup fun b => b - a
