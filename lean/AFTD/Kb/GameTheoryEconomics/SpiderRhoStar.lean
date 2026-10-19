import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_rho_star

Topic: combinatorial_games   Node: fbbb9326761a

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Theorem 4.3 and Section 6.1

The function spider_rho_star takes h : ℕ and phi : SpiderLegEnd, returning h % 2 if phi = free, and h otherwise.
-/

/-- Value of a detached run of h edges with free near end and given far end condition. -/
def spider_rho_star (h : ℕ) (phi : SpiderLegEnd) : ℕ :=
  match phi with
  | .free => h % 2
  | _ => h
