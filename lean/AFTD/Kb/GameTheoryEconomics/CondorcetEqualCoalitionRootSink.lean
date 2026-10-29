import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_equal_coalition_root_sink

Topic: social_choice   Node: 56e801959f80

Provenance: helper lemma. IN-339 supporting step for the OP-19 campaign. Strict definition: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are verification and coalition-closure helpers; no new dimension bound or research advance is asserted.

In a positive finite electorate, let a family of challenger claims all have exactly the same voter coalition as one claim with at least half support. Every nonempty finite subfamily of those claims has a challenger whose committee contains no challenger of that subfamily. This is an acyclicity necessity for pooled coalitions, not a winning-set guarantee.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_equal_coalition_root_sink
    (ι : Type*) [DecidableEq ι] (n m : ℕ) (hn : 0 < n)
    (P : Fin n → Equiv.Perm (Fin m))
    (S : ι → Finset (Fin m)) (f : ι → Fin m)
    (I : Finset ι) (i₀ : ι)
    (hbad : n ≤ 2 * (univ.filter fun v => ∀ c ∈ S i₀, P v (f i₀) < P v c).card)
    (heq : ∀ i ∈ I, ∀ v, (∀ c ∈ S i, P v (f i) < P v c) ↔
        (∀ c ∈ S i₀, P v (f i₀) < P v c)) :
    ∀ J ⊆ I, J.Nonempty → ∃ i ∈ J, ∀ j ∈ J, f j ∉ S i := by
  classical
  have hpos : 0 < (univ.filter fun v => ∀ c ∈ S i₀, P v (f i₀) < P v c).card := by
    omega
  obtain ⟨v, hv⟩ := card_pos.mp hpos
  have hv₀ := (mem_filter.mp hv).2
  intro J hJI hJ
  obtain ⟨i, hi, hmax⟩ := J.exists_max_image (fun i => P v (f i)) hJ
  refine ⟨i, hi, ?_⟩
  intro j hj hmem
  have hvi := (heq i (hJI hi) v).mpr hv₀
  exact (not_lt_of_ge (hmax j hj)) (hvi (f j) hmem)

-- A visible three-claim cycle in one coalition already excludes feasibility.
