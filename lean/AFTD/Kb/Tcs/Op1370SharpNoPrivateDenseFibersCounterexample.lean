import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op1370_sharp_no_private_dense_fibers_counterexample

Topic: combinatorics   Node: 963850e59ffe

Provenance: original. Related work: A counterexample to a sparse-fiber approach to the no-private stability case of Conjecture 4.3 of arXiv:2611.12199.

There exist three nonempty uncomplemented mutually strongly incomparable families of subsets of Fin 7. For every coordinate, some two distinct families contain sets including it, and some two distinct families contain sets excluding it. The sum of their sizes is 62. For each coordinate x, at least fourteen arbitrary subsets R of Fin 7 excluding x satisfy that both R and R union {x} belong to the union of the families.
-/

def op1370_sharp_no_private_dense_fibers_counterexample_b (m : Nat) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => m.testBit i.val)

def op1370_sharp_no_private_dense_fibers_counterexample_A0 : Finset (Finset (Fin 7)) :=
  ({3,7,11,18,19,21,22,23,26,35,39,49,50,51,53,54,55,67,81,82,83} : Finset Nat).image
    op1370_sharp_no_private_dense_fibers_counterexample_b

def op1370_sharp_no_private_dense_fibers_counterexample_A1 : Finset (Finset (Fin 7)) :=
  ({12,13,14,28,40,41,42,44,45,46,56,60,68,69,70,72,73,74,76,77,78,84,88,92,96,97,98,100,101,102,104,105,106,108,109,110,112,116,120,124} : Finset Nat).image
    op1370_sharp_no_private_dense_fibers_counterexample_b

def op1370_sharp_no_private_dense_fibers_counterexample_A2 : Finset (Finset (Fin 7)) :=
  ({25} : Finset Nat).image op1370_sharp_no_private_dense_fibers_counterexample_b

def op1370_sharp_no_private_dense_fibers_counterexample_fam : Fin 3 → Finset (Finset (Fin 7)) :=
  ![op1370_sharp_no_private_dense_fibers_counterexample_A0,
    op1370_sharp_no_private_dense_fibers_counterexample_A1,
    op1370_sharp_no_private_dense_fibers_counterexample_A2]

theorem op1370_sharp_no_private_dense_fibers_counterexample : ∃ 𝒜 : Fin 3 → Finset (Finset (Fin 7)), (∀ i, (𝒜 i).Nonempty) ∧ (∀ i, is_uncomplemented (𝒜 i)) ∧ strongly_incomparable 𝒜 ∧ (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) ∧ (∀ x, ∃ i j : Fin 3, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) ∧ (∑ i, (𝒜 i).card) = 62 ∧ ∀ x, 14 ≤ (((Finset.univ.biUnion 𝒜).filter (fun S => x ∉ S)) ∩ (((Finset.univ.biUnion 𝒜).filter (fun S => x ∈ S)).image (fun S => S.erase x))).card := by
  refine ⟨op1370_sharp_no_private_dense_fibers_counterexample_fam, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · simp only [is_uncomplemented]
    decide
  · simp only [strongly_incomparable]
    decide
  · decide
  · decide
  · decide
  · decide
