import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize
import AFTD.Kb.Tcs.In715DeficitProper

/-!
# in715_deficit_cover

Topic: graphs   Node: 95d20a3faf52

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_cover : ∀ t : Finset (Fin 14), G.IsNClique 3 t → ∃ e ∈ C, e ∈ t.sym2 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  by_contra hn
  push_neg at hn
  have habG : G.Adj a b := ht.isClique (by simp) (by simp) hab
  have hacG : G.Adj a c := ht.isClique (by simp) (by simp) hac
  have hbcG : G.Adj b c := ht.isClique (by simp) (by simp) hbc
  have habC : s(a,b) ∉ C := by intro h; exact hn _ h (by simp [Finset.mem_sym2_iff])
  have hacC : s(a,c) ∉ C := by intro h; exact hn _ h (by simp [Finset.mem_sym2_iff])
  have hbcC : s(b,c) ∉ C := by intro h; exact hn _ h (by simp [Finset.mem_sym2_iff])
  have hab' := in715_deficit_proper a b habG habC
  have hac' := in715_deficit_proper a c hacG hacC
  have hbc' := in715_deficit_proper b c hbcG hbcC
  cases hA : color a <;> cases hB : color b <;> cases hC : color c <;> simp_all
