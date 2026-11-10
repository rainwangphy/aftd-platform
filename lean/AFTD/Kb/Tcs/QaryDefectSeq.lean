import AFTD.Prelude

/-!
# qary_defect_seq

Topic: information   Node: d3346b3fce61

Provenance: formalization of a published result. Source: knowledgebase

The infinite sequence over Fin q with defect spacing B and alphabet size q ≥ 2 whose initial q symbols are 0, ..., q-1 and for i ≥ q repeats the symbol from q-1 steps earlier when B divides i - q + 1, and otherwise takes the unique alphabet symbol absent from the preceding q-1 symbols.
-/

/-- The deterministic defect sequence over Fin q with block period B. -/
def qary_defect_seq (q B : ℕ) (hq : 2 ≤ q) : ℕ → Fin q := fun i =>
  if hi : i < q then
    ⟨i, by omega⟩
  else
    if B ∣ i - q + 1 then
      qary_defect_seq q B hq (i - (q - 1))
    else
      let absent := (List.finRange q).find? (fun a =>
        (List.finRange (q - 1)).all (fun j =>
          qary_defect_seq q B hq (i - 1 - j.1) != a))
      absent.getD ⟨0, by omega⟩
termination_by i => i
decreasing_by
  · omega
  · omega
