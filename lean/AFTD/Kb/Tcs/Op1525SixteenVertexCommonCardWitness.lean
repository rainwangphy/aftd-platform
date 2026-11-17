import AFTD.Prelude

/-!
# op1525_sixteen_vertex_common_card_witness

Topic: combinatorics   Node: 0eaace5ee681

Provenance: helper lemma. An explicit block-preserving card witness for the multipartite orientation obstruction in OP-1525.

For the explicit colorings of sixteen vertices in the displayed block system, there is an injective block-preserving self-map that identifies their cards switched at vertex 1 after global color exchange. Their four triple-block profiles are respectively (0,3,0,1) and (1,0,3,0), and each has three true singleton vertices.
-/

namespace OP1525ExplicitCards

def block (x : Fin 16) : ℕ :=
  if x.val < 4 then x.val else 4 + (x.val - 4) / 3

def a (x : Fin 16) : Bool := decide (x.val ∈ [1,2,3,4,7,10,13,14,15])
def b (x : Fin 16) : Bool := decide (x.val ∈ [1,2,3,7,8,10,11,13,14])
def p : Fin 16 → Fin 16 := ![2,3,0,1,9,7,8,12,10,11,15,13,14,4,5,6]
end OP1525ExplicitCards

namespace OP1525ExplicitCards

def tripleVertex (i : Fin 4) (j : Fin 3) : Fin 16 :=
  ⟨4 + 3 * i.val + j.val, by omega⟩

def tripleProfile (f : Fin 16 → Bool) (k : Fin 4) : ℕ :=
  ((Finset.univ : Finset (Fin 4)).filter (fun i =>
    ((Finset.univ : Finset (Fin 3)).filter
      (fun j => f (tripleVertex i j))).card = k.val)).card
end OP1525ExplicitCards
open OP1525ExplicitCards

theorem op1525_sixteen_vertex_common_card_witness :
    (∀ x y : Fin 16, p x = p y → x = y) ∧
    (∀ x y : Fin 16, block (p x) = block (p y) ↔ block x = block y) ∧
    (∀ x : Fin 16, xor (a x) (decide (x = 1)) =
      xor (xor (b (p x)) (decide (p x = 1))) true) ∧
    (∀ k : Fin 4, tripleProfile a k = (![0,3,0,1] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 4, tripleProfile b k = (![1,0,3,0] : Fin 4 → ℕ) k) ∧
    ((Finset.univ : Finset (Fin 4)).filter (fun x => a ⟨x.val, by omega⟩)).card = 3 ∧
    ((Finset.univ : Finset (Fin 4)).filter (fun x => b ⟨x.val, by omega⟩)).card = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
