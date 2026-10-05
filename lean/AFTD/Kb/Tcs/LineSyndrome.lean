import AFTD.Prelude

/-!
# line_syndrome

Topic: quantum   Node: 2985e568455a

The syndrome of the line cubic form assigns 1 to adjacent triples {i, i+1, i+2} and 0 to all other subsets of Fin n.
-/

/-- The syndrome of the line cubic form, supported on adjacent index triples. -/
def line_syndrome (n : ℕ) (A : Finset (Fin n)) : ZMod 2 := if ∃ i : Fin (n - 2), A = {⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩, ⟨i.val + 2, by omega⟩} then 1 else 0
