import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# cyclic_latin_market

Topic: matching_markets   Node: b09e9ea8e730

Provenance: formalization of a published result. Source: Benjamin, Converse, Krieger (1995)

For an ordering a of Z/nZ, the opposed cyclic Latin marriage market has men and women Z/nZ where man i ranks woman j by increasing rank L_a(i,j), and woman j ranks man i by decreasing rank L_a(i,j), where L_a(i,j) is the index r with i + j = a_r.
-/

/-- The opposed cyclic Latin marriage market associated with an ordering a of Z/nZ. -/
def cyclic_latin_market (n : ℕ) (a : Fin n ≃ ZMod n) :
    MarriageMarket (ZMod n) (ZMod n) where
  pref_m i j j' := (a.symm (i + j) : ℕ) < (a.symm (i + j') : ℕ)
  pref_w j i i' := (a.symm (i' + j) : ℕ) < (a.symm (i + j) : ℕ)
