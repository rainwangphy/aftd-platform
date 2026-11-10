import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.In715SharpWitnessCount
import AFTD.Kb.Tcs.In715Wok0
import AFTD.Kb.Tcs.In715Wok1
import AFTD.Kb.Tcs.In715Wok2
import AFTD.Kb.Tcs.In715Wok3
import AFTD.Kb.Tcs.In715Wok4
import AFTD.Kb.Tcs.In715Wok5
import AFTD.Kb.Tcs.In715Wcover0
import AFTD.Kb.Tcs.In715Wcover1
import AFTD.Kb.Tcs.In715Wcover2
import AFTD.Kb.Tcs.In715Wcover3
import AFTD.Kb.Tcs.In715Wcover4
import AFTD.Kb.Tcs.In715Wcover5
import AFTD.Kb.Tcs.In715Wcover6

/-!
# simple_graph_in693_ten_seed_pair_stable

Topic: graphs   Node: 1a3b833cb72e

Provenance: helper lemma. Fifty-four finite packing witnesses in experiment 20303; the Lean kernel checks their coverage and disjointness.

Deleting any two distinct edges of the ten-vertex seed leaves its triangle packing number equal to eight.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem sharp_W_ok : ∀ q ∈ sharp_W, q.2.toFinset.card = 8 ∧ (∀ t ∈ q.2, t ∈ sharp_T) ∧ (∀ a ∈ q.2, ∀ b ∈ q.2, a ≠ b → (a ∩ b).card ≤ 1) ∧ (∀ e ∈ q.1, ∀ t ∈ q.2, e ∉ t.sym2) := by
  intro q h
  change q ∈ in715_W0 ++ in715_W1 ++ in715_W2 ++ in715_W3 ++ in715_W4 ++ in715_W5 at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact in715_Wok0 q h
          · exact in715_Wok1 q h
        · exact in715_Wok2 q h
      · exact in715_Wok3 q h
    · exact in715_Wok4 q h
  · exact in715_Wok5 q h
theorem sharp_W_cover : ∀ e ∈ sharp_EL, ∀ f ∈ sharp_EL, ∃ q ∈ sharp_W, e ∈ q.1 ∧ f ∈ q.1 := by
  intro e he f hf
  have hsplit : sharp_EL = (sharp_EL.drop 0).take 5 ++ (sharp_EL.drop 5).take 5 ++ (sharp_EL.drop 10).take 5 ++ (sharp_EL.drop 15).take 5 ++ (sharp_EL.drop 20).take 5 ++ (sharp_EL.drop 25).take 5 ++ (sharp_EL.drop 30).take 5 := by decide +kernel
  have h : e ∈ (sharp_EL.drop 0).take 5 ++ (sharp_EL.drop 5).take 5 ++ (sharp_EL.drop 10).take 5 ++ (sharp_EL.drop 15).take 5 ++ (sharp_EL.drop 20).take 5 ++ (sharp_EL.drop 25).take 5 ++ (sharp_EL.drop 30).take 5 := hsplit ▸ he
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact in715_Wcover0 e h f hf
            · exact in715_Wcover1 e h f hf
          · exact in715_Wcover2 e h f hf
        · exact in715_Wcover3 e h f hf
      · exact in715_Wcover4 e h f hf
    · exact in715_Wcover5 e h f hf
  · exact in715_Wcover6 e h f hf
lemma sharp_edge_mem {g : Sym2 (Fin 10)} (h : g ∈ sharp_G.edgeSet) : g ∈ sharp_EL := by
  induction g using Sym2.ind with
  | _ a b =>
    have h1 := ((SimpleGraph.mem_edgeSet sharp_G).mp h).1
    exact List.mem_toFinset.mp h1

lemma sharp_del_clique {t : Finset (Fin 10)} {e f : Sym2 (Fin 10)}
    (h : sharp_G.IsNClique 3 t) (he : ¬ ∀ x ∈ e, x ∈ t) (hf : ¬ ∀ x ∈ f, x ∈ t) :
    (sharp_G.deleteEdges {e,f}).IsNClique 3 t := by
  refine ⟨?_, h.card_eq⟩
  intro a ha b hb hab
  refine (SimpleGraph.deleteEdges_adj).mpr ⟨h.isClique ha hb hab, ?_⟩
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · apply he
    rw [← hmem]
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  · apply hf
    rw [← hmem]
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

theorem sharp_stable : ∀ e f : Sym2 (Fin 10), e ∈ sharp_G.edgeSet → f ∈ sharp_G.edgeSet →
    e ≠ f → simple_graph_triangle_packing_number (sharp_G.deleteEdges {e,f}) =
      simple_graph_triangle_packing_number sharp_G := by
  intro e f he hf hne
  rw [sharp_pack_eq]
  obtain ⟨q, hq, hqe, hqf⟩ := sharp_W_cover e (sharp_edge_mem he) f (sharp_edge_mem hf)
  obtain ⟨hc, ht, hp, hav⟩ := sharp_W_ok q hq
  unfold simple_graph_triangle_packing_number
  refine IsGreatest.csSup_eq ⟨⟨q.2.toFinset, ?_, ?_, hc⟩, ?_⟩
  · intro t ht'
    have ht'' := List.mem_toFinset.mp ht'
    apply sharp_del_clique (sharp_T_clique t (ht t ht''))
    · intro h; exact hav e hqe t ht'' (Finset.mem_sym2_iff.mpr h)
    · intro h; exact hav f hqf t ht'' (Finset.mem_sym2_iff.mpr h)
  · intro a ha b hb hab
    exact hp a (List.mem_toFinset.mp (Finset.mem_coe.mp ha))
      b (List.mem_toFinset.mp (Finset.mem_coe.mp hb)) hab
  · rintro k ⟨T, hT, hP, rfl⟩
    exact sharp_nu_le T (fun t ht' => (hT t ht').mono (SimpleGraph.deleteEdges_le _)) hP

theorem simple_graph_in693_ten_seed_pair_stable : ∀ e f : Sym2 (Fin 10), e ∈ sharp_G.edgeSet → f ∈ sharp_G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (sharp_G.deleteEdges {e,f}) = simple_graph_triangle_packing_number sharp_G := by exact sharp_stable
