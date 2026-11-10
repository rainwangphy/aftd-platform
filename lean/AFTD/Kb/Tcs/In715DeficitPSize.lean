import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# in715_deficit_p_size

Topic: graphs   Node: 080ee0b0c879

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace In701Deficit14
def E : Finset (Sym2 (Fin 14)) := {s(0,1), s(0,4), s(0,5), s(0,6), s(0,7), s(0,8), s(0,9), s(0,10), s(0,11), s(0,12), s(1,2), s(1,5), s(1,6), s(1,7), s(1,8), s(1,9), s(1,10), s(1,11), s(1,13), s(2,3), s(2,5), s(2,6), s(2,7), s(2,8), s(2,9), s(2,10), s(3,4), s(3,5), s(3,6), s(3,7), s(3,8), s(3,10), s(4,5), s(4,6), s(4,7), s(4,8), s(4,9), s(4,10), s(9,11), s(11,12), s(11,13)}
def G : SimpleGraph (Fin 14) where
  Adj u v := s(u,v) ∈ E ∧ u ≠ v
  symm := ⟨fun u v h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.2 rfl⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ E ∧ _ ≠ _))
def P : Finset (Finset (Fin 14)) := {{0,1,5}, {1,2,6}, {2,3,7}, {3,4,8}, {0,4,9}, {0,11,12}, {1,11,13}}
def C : Finset (Sym2 (Fin 14)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(0,4), s(0,11), s(1,11)}
def Z : Finset (Finset (Fin 14)) := {{0,1,9}, {1,2,9}, {0,4,9}, {0,9,11}, {1,9,11}}
def X : Finset (Finset (Fin 14)) := {{0,1,10}, {1,2,10}, {2,3,10}, {3,4,10}, {0,4,10}}
def color (v : Fin 14) : Bool := decide (v ∈ ({0,1,2,3,4,11} : Finset (Fin 14)))
end In701Deficit14

theorem in715_deficit_p_size : In701Deficit14.P.card = 7 := by decide +kernel
