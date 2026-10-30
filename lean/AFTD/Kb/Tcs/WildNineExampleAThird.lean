import AFTD.Prelude

/-!
# wild_nine_example_a_third

Topic: graphs   Node: 47e0299b5c2b

Provenance: helper lemma. IN-364 / OP-306, continuation of the finite weighted-partition route for https://arxiv.org/html/2610.22142v1, Sections3.3 and6. Standard permutation-orbit background: Matchings and Representation Theory (2018), Section4.10, https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content. The witness triple system is standard incidence data; these are route helpers or finite method diagnostics. No wild-number bound, new exact sharpness case, general sign theorem, or research advance is claimed.

For the explicit normalized nine-vertex array A, the sum over all 280 canonical triple partitions of D(D-1)(D-2) is 288. Here D counts colors closing at least one of the three triple blocks; the arrays and finite partition family are explicit computable definitions. This is a certificate for a method diagnostic, not a wild-number claim.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000


abbrev wild_nine_first (A : Fin 9 → Fin 9 → Fin 9) : Prop :=
 (∀ a, A a a = a) ∧ (∀ a b, A a b = A b a) ∧
 (∀ a b c, A a b = A a c → b = c)


def wild_nine_parts : Finset (Finset (Fin 9) × Finset (Fin 9)) :=
 ((univ : Finset (Fin 9)).powersetCard 3 |>.filter fun T => (0 : Fin 9) ∈ T).biUnion
  fun T => (((univ \ T).powersetCard 3).filter fun U =>
    ∀ v ∈ univ \ (T ∪ U), ∃ u ∈ U, u < v).image fun U => (T,U)


def wild_nine_blocks (P : Finset (Fin 9) × Finset (Fin 9)) : Finset (Finset (Fin 9)) :=
 {P.1,P.2,univ \ (P.1 ∪ P.2)}


abbrev wild_nine_bad (A : Fin 9 → Fin 9 → Fin 9)
    (P : Finset (Fin 9) × Finset (Fin 9)) (c : Fin 9) : Prop :=
 ∃ B ∈ wild_nine_blocks P, ∀ u ∈ B, ∀ v ∉ B, A u v ≠ c


def wild_nine_bad_count (A : Fin 9 → Fin 9 → Fin 9)
    (P : Finset (Fin 9) × Finset (Fin 9)) : ℕ :=
 (univ.filter fun c => wild_nine_bad A P c).card


def wild_nine_third_sum (A : Fin 9 → Fin 9 → Fin 9) : ℕ :=
 ∑ P ∈ wild_nine_parts, let d := wild_nine_bad_count A P; d*(d-1)*(d-2)


def wild_nine_pair_count (A : Fin 9 → Fin 9 → Fin 9) (i j : Fin 9) : ℕ :=
 (wild_nine_parts.filter fun P => wild_nine_bad A P i ∧ wild_nine_bad A P j).card


def wild_nine_pair_profile (A : Fin 9 → Fin 9 → Fin 9) : Multiset ℕ :=
 (((univ : Finset (Fin 9 × Fin 9)).filter fun z => z.1 < z.2).val.map
   fun z => wild_nine_pair_count A z.1 z.2)


def wild_nine_example_a : Fin 9 → Fin 9 → Fin 9 := ![![0,2,8,7,5,6,3,4,1],![2,1,7,5,8,3,0,6,4],![8,7,2,6,3,4,1,0,5],![7,5,6,3,1,2,4,8,0],![5,8,3,1,4,0,7,2,6],![6,3,4,2,0,5,8,1,7],![3,0,1,4,7,8,6,5,2],![4,6,0,8,2,1,5,7,3],![1,4,5,0,6,7,2,3,8]]


def wild_nine_example_b : Fin 9 → Fin 9 → Fin 9 := ![![0,4,7,8,5,6,3,2,1],![4,1,8,5,2,3,0,6,7],![7,8,2,6,3,0,4,1,5],![8,5,6,3,1,2,7,4,0],![5,2,3,1,4,7,8,0,6],![6,3,0,2,7,5,1,8,4],![3,0,4,7,8,1,6,5,2],![2,6,1,4,0,8,5,7,3],![1,7,5,0,6,4,2,3,8]]


def wild_nine_witness_multiplicity (A : Fin 9 → Fin 9 → Fin 9) (T : Finset (Fin 9)) : ℕ :=
 ((univ : Finset (Fin 9 × Fin 9)).filter fun z =>
   z.1 < z.2 ∧ ({z.1,z.2,A z.1 z.2} : Finset (Fin 9)) = T).card


def wild_nine_witness_profile (A : Fin 9 → Fin 9 → Fin 9) : Multiset ℕ :=
 (((univ : Finset (Fin 9)).powersetCard 3).val.map fun T => wild_nine_witness_multiplicity A T)


theorem wild_nine_example_a_ok : wild_nine_first wild_nine_example_a := by
  decide +kernel

theorem wild_nine_example_b_ok : wild_nine_first wild_nine_example_b := by
  decide +kernel

theorem wild_nine_parts_card : wild_nine_parts.card = 280 := by
  decide +kernel

theorem wild_nine_example_a_third : wild_nine_third_sum wild_nine_example_a = 288 := by
  decide +kernel
