import AFTD.Prelude

/-!
# wild_bundled_leaf_packing_small_obstruction

Topic: graphs   Node: 3c0a81d78f16

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

There is a normalized symmetric Latin array of order nine with the four specified color-zero pairs, such that every two disjoint pair-role leaves either have an invalid triple or share an internal nonzero color. Yet the same array has an explicit rooted partition into three triples whose quotient is connected in every color. Thus the blanket two-leaf bundled-rainbow restriction is unnecessary in this known base case. This does not refute its n>=13 variant or the wild-number conjecture.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
private def in342_bundled_nine_data : Array (Array (Fin 9)) := #[#[0,8,4,6,7,3,1,2,5],
#[8,1,0,4,5,7,3,6,2],
#[4,0,2,5,1,6,7,8,3],
#[6,4,5,3,0,8,2,1,7],
#[7,5,1,0,4,2,8,3,6],
#[3,7,6,8,2,5,0,4,1],
#[1,3,7,2,8,0,6,5,4],
#[2,6,8,1,3,4,5,7,0],
#[5,2,3,7,6,1,4,0,8]]
private def in342_bundled_nine_matrix : Fin 9 → Fin 9 → Fin 9 :=
  fun u v => (in342_bundled_nine_data[u.val]!)[v.val]!

theorem wild_bundled_leaf_packing_small_obstruction :
    ∃ A : Fin 9 → Fin 9 → Fin 9,
      (∀ u, A u u=u) ∧ (∀ u v,A u v=A v u) ∧
      (∀ u,Function.Injective (A u)) ∧
      (let a : Fin 4 → Fin 9 := fun i => ⟨2*i.val+1,by omega⟩
       let b : Fin 4 → Fin 9 := fun i => ⟨2*i.val+2,by omega⟩
       (∀ i,A (a i) (b i)=0) ∧
       (∀ i j u v : Fin 4, i≠j → u≠v →
         Disjoint ({i,j} : Finset (Fin 4)) {u,v} → ∀ s t : Bool,
           let z := if s then b j else a j
           let z' := if t then b v else a v
           A (a i) z=b i ∨ A (b i) z=a i ∨
           A (a u) z'=b u ∨ A (b u) z'=a u ∨
           ¬ Disjoint ({A (a i) z,A (b i) z} : Finset (Fin 9))
             {A (a u) z',A (b u) z'})) ∧
      (∃ (p : Fin 9 → Fin 3) (r : Fin 3 → Fin 9),
        (∀ t,p (r t)=t) ∧ (∀ t,(univ.filter fun v => p v=t).card=3) ∧
        ∀ (i : Fin 9) (S : Finset (Fin 3)), S.Nonempty → S≠univ →
          ∃ u v : Fin 9,u≠v ∧ p u∈S ∧ p v∉S ∧ A u v=i) := by
  refine ⟨in342_bundled_nine_matrix,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · dsimp only
    constructor <;> decide +kernel
  · refine ⟨![0,0,1,0,1,2,1,2,2],![0,2,5],?_,?_,?_⟩
    · decide +kernel
    · decide +kernel
    · decide +kernel
