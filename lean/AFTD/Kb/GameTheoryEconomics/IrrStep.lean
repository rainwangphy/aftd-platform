import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# irr_step

Topic: fair_division   Node: 10b917f86585

Provenance: formalization of a published result. Source: arXiv:2610.23040 Sec. 2 (Iterated setting) and Sec. 3 (restricted manipulations)

One step of iterated picking sequences restricted to admissible bids adm: some agent i that has a strictly profitable admissible manipulation changes its bid to a best response among its admissible bids, the other bids unchanged. Utilities are additive with item values v.
-/

/-- One step of the iterated picking-sequence dynamics `IPS_π` restricted to the admissible bids `adm b i`: an agent `i` with a strictly profitable admissible manipulation replaces its bid by a best response among its admissible bids; the other bids are unchanged. Utilities are additive with item values `v`. -/
def irr_step {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (v : N → G → ℝ) (seq : List N) (adm : (N → Fin m ≃ G) → N → (Fin m ≃ G) → Prop)
    (b b' : N → Fin m ≃ G) : Prop :=
  ∃ i : N,
    (∃ r, adm b i r ∧ ∑ g ∈ picking_sequence_outcome seq b i, v i g <
        ∑ g ∈ picking_sequence_outcome seq (Function.update b i r) i, v i g) ∧
    ∃ r, adm b i r ∧ b' = Function.update b i r ∧
      ∀ r', adm b i r' → ∑ g ∈ picking_sequence_outcome seq (Function.update b i r') i, v i g ≤
        ∑ g ∈ picking_sequence_outcome seq b' i, v i g
