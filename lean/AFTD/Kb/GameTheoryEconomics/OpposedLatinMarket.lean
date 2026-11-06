import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# opposed_latin_market

Topic: matching_markets   Node: 950ebd98b98b

Provenance: formalization of a published result. Source: arXiv:2609.17418, Section 1.2

The strict opposed Latin marriage market associated with an n × n Latin square L: man i ranks woman j at position L(i,j)+1, and woman j ranks man i at position n-L(i,j), with smaller rank preferred.
-/

/-- The strict opposed Latin marriage market associated with an n x n Latin square L: man i ranks woman j at position L(i,j)+1, and woman j ranks man i at position n-L(i,j). -/
def opposed_latin_market {n : ℕ} (L : Fin n → Fin n → Fin n) :
    MarriageMarket (Fin n) (Fin n) where
  pref_m i j j' := (L i j : ℕ) < (L i j' : ℕ)
  pref_w j i i' := n - (L i j : ℕ) < n - (L i' j : ℕ)
