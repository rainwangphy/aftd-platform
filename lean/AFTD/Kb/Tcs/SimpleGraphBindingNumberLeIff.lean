import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphBindingNumber

/-!
# simple_graph_binding_number_le_iff

Topic: graphs   Node: 82bad4c43a9e

Provenance: helper lemma. sanity lemma for simple_graph_binding_number; serves OP-422

For a graph on a nonempty finite vertex set, bind(G) ≤ c iff some nonempty S with N(S) ≠ V has |N(S)| ≤ c|S| (the infimum is a minimum over a finite nonempty family: every singleton is admissible since v ∉ N(v)).
-/

theorem simple_graph_binding_number_le_iff {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    simple_graph_binding_number G ≤ c ↔
      ∃ S : Finset V, S.Nonempty ∧ S.biUnion (fun v => G.neighborFinset v) ≠ Finset.univ ∧
        ((S.biUnion (fun v => G.neighborFinset v)).card : ℝ) ≤ c * S.card := by
  let ι := {S : Finset V // S.Nonempty ∧ S.biUnion (fun v => G.neighborFinset v) ≠ Finset.univ}
  have : Nonempty ι := by
    inhabit V
    refine ⟨⟨{default}, Finset.singleton_nonempty _, ?_⟩⟩
    intro h
    have hnv : (default : V) ∉ ({default} : Finset V).biUnion (fun u => G.neighborFinset u) := by simp
    rw [h] at hnv
    exact hnv (Finset.mem_univ _)
  let f : ι → ℝ := fun S => ((S.1.biUnion (fun v => G.neighborFinset v)).card : ℝ) / S.1.card
  change ⨅ S : ι, f S ≤ c ↔ _
  constructor
  · intro h
    obtain ⟨S, hS⟩ : ∃ S : ι, f S = ⨅ S : ι, f S := exists_eq_ciInf_of_finite
    rw [← hS] at h
    refine ⟨S.1, S.2.1, S.2.2, ?_⟩
    have hcard : 0 < (S.1.card : ℝ) := Nat.cast_pos.mpr S.2.1.card_pos
    exact (div_le_iff₀ hcard).mp h
  · rintro ⟨S, hne, huniv, hle⟩
    let s : ι := ⟨S, ⟨hne, huniv⟩⟩
    have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    have hfs : f s ≤ c := (div_le_iff₀ hcard).mpr hle
    exact ciInf_le_of_le (Finite.bddBelow_range f) s hfs
