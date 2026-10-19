import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_rho

Topic: combinatorial_games   Node: d765586a588f

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Theorem 4.3 and Section 6.1

The function spider_rho takes h : ℕ and delta, phi : SpiderLegEnd, returning h if phi = free; if phi = inward, it returns h % 2 when delta = inward, and (if h ≥ 2 ∧ h % 2 = 0 then 1 else 0) otherwise; if phi = outward, it returns h % 2 when delta = outward, and (if h ≥ 2 ∧ h % 2 = 0 then 1 else 0) otherwise.
-/

/-- Value of a detached run of h edges with given near and far end conditions. -/
def spider_rho (h : ℕ) (delta : SpiderLegEnd) (phi : SpiderLegEnd) : ℕ :=
  match phi with
  | .free => h
  | .inward => if delta == .inward then h % 2 else (if h ≥ 2 ∧ h % 2 == 0 then 1 else 0)
  | .outward => if delta == .outward then h % 2 else (if h ≥ 2 ∧ h % 2 == 0 then 1 else 0)
