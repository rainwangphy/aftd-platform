import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.InstFintypeColoredRootedTree
import AFTD.Kb.Tcs.InstDecEqColoredRootedTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IntervalFamily

Topic: data_structures   Node: c6eafb49b879

Provenance: formalization of a published result. Source: arXiv:2611.03620 Definition 2.2

An interval family for a colored tree consists of an injective mapping from vertices to integers and a laminar family of non-empty integer intervals, where each vertex owns at most R intervals.
-/

/-- An interval family for a colored tree with at most R intervals per vertex. -/
structure IntervalFamily (T : ColoredRootedTree) (R : ℕ) where
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  interval : ι → Set ℤ
  interval_icc : ∀ i : ι, ∃ a b : ℤ, a ≤ b ∧ interval i = Set.Icc a b
  owner : ι → T.V
  owner_bound : ∀ v : T.V, (Finset.univ.filter (fun i : ι => owner i = v)).card ≤ R
  laminar : ∀ i j : ι, interval i ⊆ interval j ∨ interval j ⊆ interval i ∨ Disjoint (interval i) (interval j)
  id : T.V → ℤ
  id_inj : Function.Injective id
