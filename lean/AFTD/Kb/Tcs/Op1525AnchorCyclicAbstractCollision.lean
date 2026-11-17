import AFTD.Prelude

/-!
# op1525_anchor_cyclic_abstract_collision

Topic: combinatorics   Node: e7306914efc9

Provenance: helper lemma. A fixed-vertex permutation-action obstruction for the equal-balance deletion reduction in OP-1525; the cyclic action is not asserted to be an undirected graph automorphism group.

On seven cyclically permuted vertices with an eighth vertex fixed, the equal-size Boolean colorings with true sets {0,1,3,7} and {0,1,5,7} have matching one-vertex switching decks up to cyclic rotations and global color exchange, but are not equivalent under those symmetries. A reflection fixing the eighth vertex does identify the colorings.
-/

namespace OP1525AnchorCyclic

def rot (t : Fin 7) (x : Fin 8) : Fin 8 :=
  if x.val < 7 then ⟨(x.val + t.val) % 7, by have h := Nat.mod_lt (x.val + t.val) (by decide : 0 < 7); omega⟩ else 7

def refl (t : Fin 7) (x : Fin 8) : Fin 8 :=
  if x.val < 7 then ⟨(t.val + 7 - x.val) % 7, by have h := Nat.mod_lt (t.val + 7 - x.val) (by decide : 0 < 7); omega⟩ else 7

def a (x : Fin 8) : Bool := decide (x.val ∈ [0,1,3,7])
def b (x : Fin 8) : Bool := decide (x.val ∈ [0,1,5,7])
def matchCard : Fin 8 → Fin 8 := ![1,0,6,5,4,3,7,2]
end OP1525AnchorCyclic
open OP1525AnchorCyclic

theorem op1525_anchor_cyclic_abstract_collision :
    (∀ x y : Fin 8, matchCard x = matchCard y → x = y) ∧
    (∀ t : Fin 7, ∀ x y : Fin 8, rot t x = rot t y → x = y) ∧
    (∀ x : Fin 8, rot 0 x = x) ∧
    (∀ s t : Fin 7, ∀ x : Fin 8, rot s (rot t x) = rot (s + t) x) ∧
    (∀ t : Fin 7, rot t 7 = 7) ∧
    (∀ v : Fin 8, ∃ t : Fin 7, ∃ c : Bool, ∀ x : Fin 8,
      xor (a (rot t x)) (decide (rot t x = v)) =
      xor (xor (b x) (decide (x = matchCard v))) c) ∧
    (∀ t : Fin 7, ∀ c : Bool, ∃ x : Fin 8, a (rot t x) ≠ xor (b x) c) ∧
    (∀ x : Fin 8, a (refl 1 x) = b x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
