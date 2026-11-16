import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_repaired_coordinate_witness_counterexample

Topic: combinatorics   Node: 15b39901ee06

Provenance: original. Related work: A counterexample to the repaired fixed-coordinate witness-shadow counting route toward Conjecture 4.3 of arXiv:2611.12199.

There exist three nonempty uncomplemented mutually strongly incomparable families of subsets of Fin 6 such that, for every coordinate, some two distinct families contain sets including that coordinate and some two distinct families contain sets excluding it. Put x = 0 and V = Fin 6 with x removed. Every fiber below means an arbitrary subset R of V, whether or not R is present in a family. Call R a lower witness fiber if there are sets A and B in different families, both containing x, such that R is contained in (A intersect B) with x removed. Call R an upper witness fiber if there are sets C and D in different families, both excluding x, such that C union D is contained in R. There is exactly one lower witness fiber and exactly one upper witness fiber. Call R doubled if both R and R union {x} are present in the union of the families. Exactly two fibers are doubled. For each doubled fiber R, at least one of V minus R and (V minus R) union {x} belongs to the union of the families.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem op1370_repaired_coordinate_witness_counterexample :
  ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 6)),
    (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧
    strongly_incomparable 𝒜 ∧
    (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧
    (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧
    let x : Fin 6 := 0
    let V : Finset (Fin 6) := Finset.univ.erase x
    let U := Finset.univ.biUnion 𝒜
    let P := U.filter (fun S => x ∉ S)
    let Q := (U.filter (fun S => x ∈ S)).image (fun S => S.erase x)
    let low : Fin 3 → Finset (Finset (Fin 6)) := fun i =>
      ((𝒜 i).filter (fun A => x ∈ A)).biUnion (fun A => (A.erase x).powerset)
    let high : Fin 3 → Finset (Finset (Fin 6)) := fun i =>
      ((𝒜 i).filter (fun A => x ∉ A)).biUnion
        (fun A => (V \ A).powerset.image (fun B => A ∪ B))
    let L := (low 0 ∩ low 1) ∪ (low 0 ∩ low 2) ∪ (low 1 ∩ low 2)
    let H := (high 0 ∩ high 1) ∪ (high 0 ∩ high 2) ∪ (high 1 ∩ high 2)
    L.card = 1 ∧ H.card = 1 ∧ (P ∩ Q).card = 2 ∧
      (∀ S ∈ P ∩ Q, V \ S ∈ P ∪ Q) := by
  refine ⟨![{{1,2,5}, {1,2,3,5}, {1,2,4,5}}, {{0,1}, {0,2}, {0,1,2}}, {{3,4}, {0,3,4}, {3,4,5}, {0,3,4,5}}], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · unfold is_uncomplemented
    decide +kernel
  · unfold strongly_incomparable
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
