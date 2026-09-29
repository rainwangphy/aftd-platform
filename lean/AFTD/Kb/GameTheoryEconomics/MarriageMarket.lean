import AFTD.Prelude

/-!
# MarriageMarket

Topic: matching_markets   Node: 2f0473121e6f

A marriage market with types M and W consists of a relation pref_m : M → W → W → Prop representing men's preferences over women, and a relation pref_w : W → M → M → Prop representing women's preferences over men.
-/

/-- A two-sided marriage market with agent types M and W and preference relations. -/
structure MarriageMarket (M W : Type*) where
  pref_m : M → W → W → Prop
  pref_w : W → M → M → Prop
