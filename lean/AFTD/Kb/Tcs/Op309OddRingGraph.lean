import AFTD.Prelude

/-!
# op309_odd_ring_graph

Topic: graphs   Node: 07a883c4fc26

Provenance: helper lemma. Graph family for the parity obstruction to the chord-spacing method of https://arxiv.org/abs/2611.24297; experiments 34618 and 34620.

The ring of n ten-vertex blocks: consecutive vertices follow the cyclic ring and each block has matching chords 03, 15, 27, 48 and 69.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

open Fin.NatCast

variable {n : ℕ} [NeZero n]


def op309_odd_ring_next (v : Fin n × Fin 10) : Fin n × Fin 10 :=
  if v.2 = 9 then (v.1 + 1, 0) else (v.1, v.2 + 1)

def op309_odd_ring_previous (v : Fin n × Fin 10) : Fin n × Fin 10 :=
  if v.2 = 0 then (v.1 - 1, 9) else (v.1, v.2 - 1)

def op309_odd_ring_mate : Fin 10 → Fin 10 := ![3,5,7,0,8,1,9,2,4,6]

theorem op309_odd_ring_mate_involutive (j : Fin 10) :
    op309_odd_ring_mate (op309_odd_ring_mate j) = j := by
  fin_cases j <;> decide

theorem op309_odd_ring_next_previous (v : Fin n × Fin 10) :
    op309_odd_ring_next (op309_odd_ring_previous v) = v := by
  rcases v with ⟨i,j⟩
  fin_cases j <;> simp [op309_odd_ring_next, op309_odd_ring_previous]

def op309_odd_ring_graph {n : ℕ} [NeZero n] : SimpleGraph (Fin n × Fin 10) where
  Adj u v := v = op309_odd_ring_next u ∨ u = op309_odd_ring_next v ∨
    (u.1 = v.1 ∧ op309_odd_ring_mate u.2 = v.2)
  symm := ⟨by
    intro u v h
    rcases h with h | h | ⟨h₁,h₂⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · refine Or.inr (Or.inr ⟨h₁.symm, ?_⟩)
      rw [← h₂, op309_odd_ring_mate_involutive]⟩
  loopless := ⟨by
    intro ⟨i,j⟩
    fin_cases j <;> simp [op309_odd_ring_next, op309_odd_ring_mate]⟩
