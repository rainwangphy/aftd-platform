import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSourceTournamentQuasikernelSingleton

/-!
# digraph_nonneighborhood_kernel_no_second_layer_kernel_counterexample

Topic: graphs   Node: 0429ce1c5581

Provenance: helper lemma. Explicit finite construction and component-by-component audit in experiment 14470; it is a computational counterexample candidate to the proposed universal second-layer-kernel shortcut and is not yet Lean-verified. The cyclic core is a classical graph, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v13i1r69/pdf/.

The displayed source-free oriented twenty-vertex graph has an out-kernel in every non-neighborhood. Its only quasi-kernels are singletons in the cyclic seven-vertex core, and every such singleton has a kernel-free second out-neighborhood.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in541_join_core : Finset (Fin 20) := {0,1,2,3,4,5,6}
def in541_join_middle : Finset (Fin 20) := {7,8,9,10,11,12,13,14}
def in541_join_last : Finset (Fin 20) := {15,16,17,18,19}
def in541_join_middle_out (v : Fin 20) : Finset (Fin 20) :=
  if v = 7 then {11,13} else if v = 8 then {9,10,11} else
  if v = 9 then {7,12} else if v = 10 then {9,14} else
  if v = 11 then {10,14} else if v = 12 then {8,10,11,13,14} else
  if v = 13 then {8,9} else if v = 14 then {7,8} else ∅
def in541_join_out (v : Fin 20) : Finset (Fin 20) :=
  if v ∈ in541_join_core then
    (in541_join_core.filter fun u => u ≠ v ∧ (u.val + 7 - v.val) % 7 ∈ ({1,2,4} : Finset ℕ)) ∪
      (in541_join_middle ∪ in541_join_last)
  else if v ∈ in541_join_middle then in541_join_middle_out v ∪ in541_join_last
  else if v = 15 then {16} else ∅
def in541_join_independent (Q : Finset (Fin 20)) : Prop :=
  ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in541_join_out u
def in541_join_qk (Q : Finset (Fin 20)) : Prop :=
  in541_join_independent Q ∧ ∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in541_join_out u ∨
    ∃ z, z ∈ in541_join_out u ∧ v ∈ in541_join_out z

instance (Q : Finset (Fin 20)) : Decidable (in541_join_independent Q) := by
  unfold in541_join_independent
  infer_instance

instance (Q : Finset (Fin 20)) : Decidable (in541_join_qk Q) := by
  unfold in541_join_qk
  infer_instance

theorem digraph_nonneighborhood_kernel_no_second_layer_kernel_counterexample :
    (∀ v, v ∉ in541_join_out v) ∧
    (∀ u v, v ∈ in541_join_out u → u ∉ in541_join_out v) ∧
    (∀ v, ∃ u, v ∈ in541_join_out u) ∧
    (∀ v, ∃ K : Finset (Fin 20),
      (∀ x ∈ K, x ≠ v ∧ x ∉ in541_join_out v ∧ v ∉ in541_join_out x) ∧
      in541_join_independent K ∧
      (∀ x, x ≠ v → x ∉ in541_join_out v → v ∉ in541_join_out x →
        ∃ k ∈ K, k = x ∨ x ∈ in541_join_out k)) ∧
    (∀ v ∈ in541_join_core, in541_join_qk {v}) ∧
    (∀ Q : Finset (Fin 20), in541_join_qk Q → ∃ v ∈ in541_join_core, Q = {v}) ∧
    (∀ v ∈ in541_join_core,
      let R := Finset.univ.filter (fun x => x ≠ v ∧ x ∉ in541_join_out v)
      ∀ K : Finset (Fin 20), K ⊆ R → in541_join_independent K →
        ¬ (∀ x ∈ R, ∃ k ∈ K, k = x ∨ x ∈ in541_join_out k)) := by
  classical
  have hloop : ∀ v, v ∉ in541_join_out v := by decide
  have horient : ∀ u v, v ∈ in541_join_out u → u ∉ in541_join_out v := by decide
  have hsrc : ∀ v, ∃ u, v ∈ in541_join_out u := by decide
  have hlocal : ∀ v, ∃ K : Finset (Fin 20),
      (∀ x ∈ K, x ≠ v ∧ x ∉ in541_join_out v ∧ v ∉ in541_join_out x) ∧
      in541_join_independent K ∧
      (∀ x, x ≠ v → x ∉ in541_join_out v → v ∉ in541_join_out x →
        ∃ k ∈ K, k = x ∨ x ∈ in541_join_out k) := by
    intro v
    fin_cases v
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨∅, ?_⟩; decide
    · refine ⟨{12}, ?_⟩; decide
    · refine ⟨{7}, ?_⟩; decide
    · refine ⟨{11}, ?_⟩; decide
    · refine ⟨{7}, ?_⟩; decide
    · refine ⟨{13}, ?_⟩; decide
    · refine ⟨{7}, ?_⟩; decide
    · refine ⟨{11}, ?_⟩; decide
    · refine ⟨{13}, ?_⟩; decide
    · refine ⟨{17,18,19}, ?_⟩; decide
    · refine ⟨{17,18,19}, ?_⟩; decide
    · refine ⟨{15,18,19}, ?_⟩; decide
    · refine ⟨{15,17,19}, ?_⟩; decide
    · refine ⟨{15,17,18}, ?_⟩; decide

  have hcoreq : ∀ v ∈ in541_join_core, in541_join_qk {v} := by decide
  have hclass : ∀ Q : Finset (Fin 20), in541_join_qk Q → ∃ v ∈ in541_join_core, Q = {v} := by
    intro Q hQ
    let D : Digraph (Fin 20) := ⟨fun u v => v ∈ in541_join_out u⟩
    have htour : ∀ u ∈ in541_join_core, ∀ v ∈ in541_join_core, u ≠ v → D.Adj u v ∨ D.Adj v u := by decide
    have hcross : ∀ u ∈ in541_join_core, ∀ v, v ∉ in541_join_core → D.Adj u v ∧ ¬ D.Adj v u := by decide
    exact digraph_source_tournament_quasikernel_singleton D in541_join_core Q (by decide) htour hcross hQ.1 hQ.2
  refine ⟨hloop, horient, hsrc, hlocal, hcoreq, hclass, ?_⟩
  intro v hv
  have hv' : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by
    simpa [in541_join_core] using hv
  rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (0 : Fin 20) ∧ x ∉ in541_join_out 0)) = ({3,5,6} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({3,5,6} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({3,5,6} : Finset (Fin 20)).powerset = ({∅, {3}, {5}, {6}, {3,5}, {3,6}, {5,6}, {3,5,6}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (1 : Fin 20) ∧ x ∉ in541_join_out 1)) = ({0,4,6} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({0,4,6} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({0,4,6} : Finset (Fin 20)).powerset = ({∅, {0}, {4}, {6}, {0,4}, {0,6}, {4,6}, {0,4,6}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (2 : Fin 20) ∧ x ∉ in541_join_out 2)) = ({0,1,5} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({0,1,5} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({0,1,5} : Finset (Fin 20)).powerset = ({∅, {0}, {1}, {5}, {0,1}, {0,5}, {1,5}, {0,1,5}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (3 : Fin 20) ∧ x ∉ in541_join_out 3)) = ({1,2,6} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({1,2,6} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({1,2,6} : Finset (Fin 20)).powerset = ({∅, {1}, {2}, {6}, {1,2}, {1,6}, {2,6}, {1,2,6}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (4 : Fin 20) ∧ x ∉ in541_join_out 4)) = ({0,2,3} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({0,2,3} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({0,2,3} : Finset (Fin 20)).powerset = ({∅, {0}, {2}, {3}, {0,2}, {0,3}, {2,3}, {0,2,3}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (5 : Fin 20) ∧ x ∉ in541_join_out 5)) = ({1,3,4} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({1,3,4} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({1,3,4} : Finset (Fin 20)).powerset = ({∅, {1}, {3}, {4}, {1,3}, {1,4}, {3,4}, {1,3,4}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
  · dsimp only
    intro K hK hI hD
    have hr : (Finset.univ.filter (fun x => x ≠ (6 : Fin 20) ∧ x ∉ in541_join_out 6)) = ({2,4,5} : Finset (Fin 20)) := by decide
    rw [hr] at hK hD
    have hm : K ∈ ({2,4,5} : Finset (Fin 20)).powerset := Finset.mem_powerset.mpr hK
    have hp : ({2,4,5} : Finset (Fin 20)).powerset = ({∅, {2}, {4}, {5}, {2,4}, {2,5}, {4,5}, {2,4,5}} : Finset (Finset (Fin 20))) := by decide
    rw [hp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals revert hI hD; decide
