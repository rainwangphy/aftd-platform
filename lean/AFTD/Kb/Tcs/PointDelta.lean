import AFTD.Prelude

/-!
# point_delta

Topic: quantum   Node: ba88cd67b879

Provenance: helper lemma. step towards stabilizer_campbell_howard_iff_reed_muller

The indicator of a point β of (ZMod 2)^s is the Boolean function that equals 1 at β and 0 elsewhere.
-/

/-- The indicator function of the single point β of the cube (ZMod 2)^s. -/
noncomputable def point_delta {s : ℕ} (β : Fin s → ZMod 2) : (Fin s → ZMod 2) → ZMod 2 := fun x => if x = β then 1 else 0
