import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DaRun

/-!
# deferred_acceptance

Topic: matching_markets   Node: 88ad94e22d36

Men-proposing deferred acceptance (Gale-Shapley): the man each woman ends up with, given each man's ranking of the women and each woman's ranking of the men (0 = best).
-/

/-- Men-proposing deferred acceptance (Gale-Shapley): the man each woman ends up with. With complete rankings every man makes at most `nw` proposals, so `nm * nw` steps suffice. -/
def deferred_acceptance {nm nw : ℕ} (rm : Fin nm → Fin nw → Fin nw) (rw : Fin nw → Fin nm → Fin nm) :
    Fin nw → Option (Fin nm) :=
  da_run rm rw (nm * nw + 1) (fun _ => none) (fun _ => 0)
