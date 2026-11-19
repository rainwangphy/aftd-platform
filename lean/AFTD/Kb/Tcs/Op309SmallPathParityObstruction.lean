import AFTD.Prelude

/-!
# op309_small_path_parity_obstruction

Topic: graphs   Node: 02e09c8507bb

Provenance: helper lemma. Finite path-tiling kernel for the two-port obstruction in the OP-309 Boolean coloring route, experiments 33353 and 33354.

In the displayed thirteen-edge path model, every matching bitmask with the eight specified potential-domination conditions and every seven-bit phase assignment fail at least one of the eight corresponding parity-domination conditions.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def op309_small_path_matching (m : ℕ) : Bool := (!(m.testBit 0 && m.testBit 1) && !(m.testBit 1 && m.testBit 2) && !(m.testBit 2 && m.testBit 3) && !(m.testBit 3 && m.testBit 4) && !(m.testBit 4 && m.testBit 5) && !(m.testBit 5 && m.testBit 6) && !(m.testBit 6 && m.testBit 7) && !(m.testBit 7 && m.testBit 8) && !(m.testBit 8 && m.testBit 9) && !(m.testBit 9 && m.testBit 10) && !(m.testBit 10 && m.testBit 11) && !(m.testBit 11 && m.testBit 12))
def op309_small_path_potential (m : ℕ) : Bool := (((m.testBit 7 != m.testBit 9) || (m.testBit 9 != m.testBit 11)) && ((m.testBit 6 != m.testBit 8) || (m.testBit 8 != m.testBit 10)) && ((m.testBit 4 != m.testBit 6) || (m.testBit 6 != m.testBit 8)) && ((m.testBit 3 != m.testBit 5) || (m.testBit 5 != m.testBit 7)) && ((m.testBit 8 != m.testBit 10) || (m.testBit 10 != m.testBit 12)) && ((m.testBit 5 != m.testBit 7) || (m.testBit 7 != m.testBit 9)) && ((m.testBit 1 != m.testBit 3) || (m.testBit 3 != m.testBit 5)) && ((m.testBit 2 != m.testBit 4) || (m.testBit 4 != m.testBit 6)))
def op309_small_path_dominates (m p : ℕ) : Bool := ((((m.testBit 7 != m.testBit 9) && (p.testBit 5 != p.testBit 1)) || ((m.testBit 9 != m.testBit 11) && (p.testBit 4 != p.testBit 3))) && (((m.testBit 6 != m.testBit 8) && (p.testBit 2 != p.testBit 5)) || ((m.testBit 8 != m.testBit 10) && (p.testBit 1 != p.testBit 4))) && (((m.testBit 4 != m.testBit 6) && (p.testBit 3 != p.testBit 1)) || ((m.testBit 6 != m.testBit 8) && (p.testBit 2 != p.testBit 5))) && (((m.testBit 3 != m.testBit 5) && (p.testBit 5 != p.testBit 3)) || ((m.testBit 5 != m.testBit 7) && (p.testBit 1 != p.testBit 2))) && (((m.testBit 8 != m.testBit 10) && (p.testBit 1 != p.testBit 4)) || ((m.testBit 10 != m.testBit 12) && (p.testBit 3 != p.testBit 0))) && (((m.testBit 5 != m.testBit 7) && (p.testBit 1 != p.testBit 2)) || ((m.testBit 7 != m.testBit 9) && (p.testBit 5 != p.testBit 1))) && (((m.testBit 1 != m.testBit 3) && (p.testBit 4 != p.testBit 2)) || ((m.testBit 3 != m.testBit 5) && (p.testBit 5 != p.testBit 3))) && (((m.testBit 2 != m.testBit 4) && (p.testBit 2 != p.testBit 5)) || ((m.testBit 4 != m.testBit 6) && (p.testBit 3 != p.testBit 1))))

theorem op309_small_path_matching_classification :
    ∀ m : Fin 8192, op309_small_path_matching m.val = true →
      op309_small_path_potential m.val = true →
      m.val = 1170 ∨ m.val = 2340 ∨ m.val = 2341 ∨ m.val = 4680 ∨ m.val = 4681 ∨ m.val = 4682 ∨ m.val = 5266 := by
  decide

theorem op309_small_path_no_dominance_1170 :
    ∀ p : Fin 128, op309_small_path_dominates 1170 p.val = false := by
  decide

theorem op309_small_path_no_dominance_2340 :
    ∀ p : Fin 128, op309_small_path_dominates 2340 p.val = false := by
  decide

theorem op309_small_path_no_dominance_2341 :
    ∀ p : Fin 128, op309_small_path_dominates 2341 p.val = false := by
  decide

theorem op309_small_path_no_dominance_4680 :
    ∀ p : Fin 128, op309_small_path_dominates 4680 p.val = false := by
  decide

theorem op309_small_path_no_dominance_4681 :
    ∀ p : Fin 128, op309_small_path_dominates 4681 p.val = false := by
  decide

theorem op309_small_path_no_dominance_4682 :
    ∀ p : Fin 128, op309_small_path_dominates 4682 p.val = false := by
  decide

theorem op309_small_path_no_dominance_5266 :
    ∀ p : Fin 128, op309_small_path_dominates 5266 p.val = false := by
  decide

theorem op309_small_path_parity_obstruction (m : Fin 8192) (p : Fin 128)
    (hm : op309_small_path_matching m.val = true)
    (hp : op309_small_path_potential m.val = true)
    (hd : op309_small_path_dominates m.val p.val = true) : False := by
  have hc := op309_small_path_matching_classification m hm hp
  rcases hc with h | h | h | h | h | h | h
  · rw [h, op309_small_path_no_dominance_1170 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_2340 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_2341 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_4680 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_4681 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_4682 p] at hd
    contradiction
  · rw [h, op309_small_path_no_dominance_5266 p] at hd
    contradiction
