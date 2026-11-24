import AFTD.Prelude
import AFTD.Kb.Tcs.Op874srEnds
import AFTD.Kb.Tcs.StrongTruncationMissingColorEdgeBound
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_single_color_at_most_one_impossible

Topic: graphs   Node: 4340d1743780

Provenance: helper lemma. OP-874: single-edge repair obstruction, experiments 38435 and 38438.

On this cubic graph no compatible strong local states exist when a given color appears on at most one external edge.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
private lemma op874sr_loopless : ∀ e, ¬ (op874sr_ends e).IsDiag := by decide
private lemma op874sr_cubic : ∀ v : Fin 8,
    Set.ncard {e : Fin 12 | v ∈ op874sr_ends e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide

theorem op874_single_color_at_most_one_impossible
    (c : Fin 12 → Fin 6) (h : Fin 8 → Fin 12 → Fin 6)
    (hc : ∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → c e = c f → e=f)
    (hh : ∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → h v e = h v f → e=f)
    (hch : ∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → h v e ≠ c f)
    (hs : truncation_local_states_define_strong_coloring op874sr_ends (fun _ e => c e) h)
    (hatmost : ∀ e f, c e = 2 → c f = 2 → e=f) : False := by
  classical
  by_cases hex : ∃ e, c e = 2
  · obtain ⟨e,he⟩ := hex
    let S : Finset (Fin 8) := Finset.univ.filter fun v => v ∉ op874sr_ends e
    have hS : ∀ v ∈ S, ∀ f, v ∈ op874sr_ends f → c f ≠ 2 := by
      intro v hv f hvf hf
      have hfe : f=e := hatmost f e hf he
      subst f
      exact (Finset.mem_filter.mp hv).2 hvf
    have hb := strong_truncation_missing_color_edge_bound
      (by decide : Fintype.card (Fin 6)=6) op874sr_ends op874sr_loopless op874sr_cubic
      (fun _ f => c f) h hc hh hch hs 2 S hS
    have bad : (Finset.univ.filter fun f : Fin 12 =>
        ∃ u ∈ S, ∃ v ∈ S, op874sr_ends f = s(u,v)).card > S.card := by
      dsimp [S]
      fin_cases e <;> decide
    apply (Nat.not_lt_of_ge hb)
    convert bad using 1 <;> congr 1 <;> ext x <;> simp
  · have hn : ∀ e, c e ≠ 2 := by simpa using hex
    have hS : ∀ v ∈ (Finset.univ : Finset (Fin 8)),
        ∀ f, v ∈ op874sr_ends f → c f ≠ 2 := by
      intro v hv f hf
      exact hn f
    have hb := strong_truncation_missing_color_edge_bound
      (by decide : Fintype.card (Fin 6)=6) op874sr_ends op874sr_loopless op874sr_cubic
      (fun _ f => c f) h hc hh hch hs 2 Finset.univ hS
    have bad : (Finset.univ.filter fun f : Fin 12 =>
        ∃ u ∈ (Finset.univ : Finset (Fin 8)), ∃ v ∈ (Finset.univ : Finset (Fin 8)),
          op874sr_ends f = s(u,v)).card > (Finset.univ : Finset (Fin 8)).card := by decide
    apply (Nat.not_lt_of_ge hb)
    convert bad using 1 <;> congr 1 <;> ext x <;> simp
