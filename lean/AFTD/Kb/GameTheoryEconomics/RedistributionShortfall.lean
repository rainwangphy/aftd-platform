import AFTD.Prelude

/-!
# redistribution_shortfall

Topic: mechanism_design   Node: eefbad0ea943

Provenance: formalization of a published result. Source: scout/2610-10995-asymptotically-optimal-public-project-redistribution-withou.md:194

The shortfall function G(t) = max(1 - t, 0), representing the amount by which a total report falls short of the project cost 1.
-/

/-- The shortfall function G(t) = max(1 - t, 0) for public project redistribution. -/
noncomputable def redistribution_shortfall : ℝ → ℝ := fun t => max (1 - t) 0
