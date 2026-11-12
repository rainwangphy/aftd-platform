import AFTD.Prelude

/-!
# OnlineMatchingPolicy

Topic: online_algorithms   Node: f68ff61635ef

Provenance: formalization of a published result. Source: arXiv:2611.13571, Section 5.1

An online matching policy on n vertices is a decision rule that, given the observed edges H, unmatched vertices U, and an arriving edge e, outputs a boolean decision indicating whether to accept e.
-/

/-- An online matching policy deciding whether to accept an arriving edge given observed edges and unmatched vertices. -/
def OnlineMatchingPolicy (n : ℕ) : Type :=
  Finset (Sym2 (Fin n)) → Finset (Fin n) → Sym2 (Fin n) → Bool
