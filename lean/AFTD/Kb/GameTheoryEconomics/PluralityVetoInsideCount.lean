import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionDominatedCandidates

/-!
# plurality_veto_inside_count

Topic: social_choice   Node: e1d8d8aae6eb

Provenance: helper lemma. step towards plurality_veto_core_exact_regularization_threshold

For a profile prof, candidate a and candidate set N, the veto inside count k(N) is the number of voters whose veto down-set below a (the candidates weakly dominated by a in that voter's ranking) is contained in N.
-/

/-- Number of voters v whose dominated set coalition_dominated_candidates prof a {v} is contained in N. -/
def plurality_veto_inside_count {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (prof : V → LinearOrder C) (a : C) (N : Finset C) : ℕ := (Finset.univ.filter (fun v => coalition_dominated_candidates prof a {v} ⊆ N)).card
