import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_coeff

Topic: combinatorics   Node: 55e00892ae69

Provenance: formalization of a published result. Source: arXiv:2611.07503, Eq. (1)

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and k : ℕ, petrial_coeff G k is the cardinality of the finset of all F : Finset V such that the rank over ZMod 2 of petrial_matrix G F equals k.
-/

/-- The k-th coefficient of the partial Petrial polynomial of a simple graph. -/
noncomputable def petrial_coeff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ := ((Finset.univ : Finset (Finset V)).filter (fun F => (petrial_matrix G F).rank = k)).card
