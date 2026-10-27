import AFTD.Prelude
import AFTD.Kb.Tcs.DiffersAtOne

/-!
# differs_at_one_irrefl

Topic: combinatorics   Node: c2d4d4c399ca

Provenance: helper lemma. arXiv:2610.03808 Sec. 2.1

For any type ι and any function f : ι → ℤˣ taking values in the units of ℤ, differs_at_one f f does not hold.
-/

/-- Irreflexivity of differing at exactly one index. -/
theorem differs_at_one_irrefl {ι : Type*} (f : ι → ℤˣ) : ¬ differs_at_one f f := fun ⟨_, h, _⟩ => h rfl
