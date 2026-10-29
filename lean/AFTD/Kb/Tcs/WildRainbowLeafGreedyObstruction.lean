import AFTD.Prelude

/-!
# wild_rainbow_leaf_greedy_obstruction

Topic: graphs   Node: f3691e51a8ed

Provenance: helper lemma. IN-338 structural/repair helpers for OP-306, the prescribed-coloring conjecture in arXiv:2610.22142 Sections3.3.2 and6. Exact matching-involution balance and the method obstruction computed in experiment8464. These are certificate/method lemmas, not new wild-number bounds or research advances.

There is a symmetric idempotent15-by15 color matrix with injective rows and the prescribed seven color-zero matching pairs. Its two valid leaf cherries on role pairs(0,1) and(2,3) have four distinct nonzero internal colors8,9,10,11. Every additional leaf using two of the remaining matching-pair roles4,5,6 is invalid or repeats a used internal color, so this family is inclusion maximal. Nevertheless the same matrix admits a valid/rainbow family of three leaves with disjoint matching-pair roles.
-/

open Finset
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
private def in338_greedy_data : Array (Array (Fin 15)) := #[#[0, 10, 4, 5, 2, 1, 8, 3, 14, 6, 11, 7, 9, 12, 13],
#[10, 1, 0, 8, 3, 7, 9, 2, 6, 4, 5, 13, 14, 11, 12],
#[4, 0, 2, 9, 12, 8, 7, 1, 10, 5, 6, 14, 13, 3, 11],
#[5, 8, 9, 3, 0, 13, 10, 12, 11, 2, 7, 4, 6, 14, 1],
#[2, 3, 12, 0, 4, 14, 1, 8, 5, 11, 13, 6, 7, 9, 10],
#[1, 7, 8, 13, 14, 5, 0, 10, 9, 3, 12, 2, 11, 4, 6],
#[8, 9, 7, 10, 1, 0, 6, 11, 13, 14, 2, 12, 4, 5, 3],
#[3, 2, 1, 12, 8, 10, 11, 7, 0, 13, 14, 9, 5, 6, 4],
#[14, 6, 10, 11, 5, 9, 13, 0, 8, 12, 4, 3, 1, 7, 2],
#[6, 4, 5, 2, 11, 3, 14, 13, 12, 9, 0, 1, 10, 8, 7],
#[11, 5, 6, 7, 13, 12, 2, 14, 4, 0, 10, 8, 3, 1, 9],
#[7, 13, 14, 4, 6, 2, 12, 9, 3, 1, 8, 11, 0, 10, 5],
#[9, 14, 13, 6, 7, 11, 4, 5, 1, 10, 3, 0, 12, 2, 8],
#[12, 11, 3, 14, 9, 4, 5, 6, 7, 8, 1, 10, 2, 13, 0],
#[13, 12, 11, 1, 10, 6, 3, 4, 2, 7, 9, 5, 8, 0, 14]]
private def in338_greedy_matrix : Fin 15 → Fin 15 → Fin 15 := fun u v => (in338_greedy_data[u.val]!)[v.val]!

theorem wild_rainbow_leaf_greedy_obstruction :
    ∃ A : Fin 15 → Fin 15 → Fin 15,
      (∀ u, A u u = u) ∧ (∀ u v, A u v = A v u) ∧
      (∀ u, Function.Injective (A u)) ∧
      (let a : Fin 7 → Fin 15 := fun i => ⟨2*i.val+1, by omega⟩
       let b : Fin 7 → Fin 15 := fun i => ⟨2*i.val+2, by omega⟩
       (∀ j, A (a j) (b j) = 0) ∧
       A 1 3 = 8 ∧ A 2 3 = 9 ∧ A 5 7 = 10 ∧ A 6 7 = 11 ∧
       (∀ i j : Fin 7, 4 ≤ i.val → 4 ≤ j.val → i ≠ j → ∀ side : Bool,
         let z := if side then b j else a j
         A (a i) z = b i ∨ A (b i) z = a i ∨
           A (a i) z ∈ ({8,9,10,11} : Finset (Fin 15)) ∨
           A (b i) z ∈ ({8,9,10,11} : Finset (Fin 15))) ∧
       (∃ (α β : Fin 3 → Fin 7) (side : Fin 3 → Bool),
         Function.Injective (Sum.elim α β : Fin 3 ⊕ Fin 3 → Fin 7) ∧
         (∀ t,
           let z := if side t then b (β t) else a (β t)
           A (a (α t)) z ≠ b (α t) ∧ A (b (α t)) z ≠ a (α t)) ∧
         (∀ t u, t ≠ u →
           Disjoint
             ({A (a (α t)) (if side t then b (β t) else a (β t)),
               A (b (α t)) (if side t then b (β t) else a (β t))} : Finset (Fin 15))
             {A (a (α u)) (if side u then b (β u) else a (β u)),
               A (b (α u)) (if side u then b (β u) else a (β u))}))) := by
  refine ⟨in338_greedy_matrix, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · refine ⟨![1,2,3], ![6,4,5], ![false,true,true], ?_, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
      · decide +kernel
