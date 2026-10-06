import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DaRun

/-!
# deferred_acceptance

Topic: matching_markets   Node: 88ad94e22d36

Provenance: formalization of a published result. Source: College Admissions and the Stability of Marriage (1962), men-proposing deferred acceptance; It's Not All Black and White: Degree of Truthfulness for Risk-Avoiding Agents, arXiv:2502.18805 v3, Def. 3.1 and Sec. 8.1

Men-proposing deferred acceptance (Gale-Shapley): the man each woman ends up with, given each man's ranking of the women and each woman's ranking of the men (0 = best).
-/

/-- Men-proposing deferred acceptance (Gale-Shapley): the man each woman ends up with. With complete rankings every man makes at most `nw` proposals, so `nm * nw` steps suffice. -/
def deferred_acceptance {nm nw : ℕ} (rm : Fin nm → Fin nw → Fin nw) (rw : Fin nw → Fin nm → Fin nm) :
    Fin nw → Option (Fin nm) :=
  da_run rm rw (nm * nw + 1) (fun _ => none) (fun _ => 0)
