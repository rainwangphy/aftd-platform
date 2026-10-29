import AFTD.Prelude
import AFTD.Kb.Tcs.WildNormalizedArrayPairWitnessCard
import AFTD.Kb.Tcs.WildNormalizedArrayVertexWitnessCard
import AFTD.Kb.Tcs.WildThreeUniformDisjointPairCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# wild_normalized_array_disjoint_witness_pair_count

Topic: graphs   Node: 406411a30852

Provenance: helper lemma. IN-359 / OP-306 helper for the uniform weighted-moment route. The associated threefold triple system is standard: Compatible factorizations and three-fold triple systems (2006), construction in the proof of Theorem4.1, https://citeseerx.ist.psu.edu/document?doi=58cc9f2b7c3862f0964a05e0ac1529b9c9de8e5e&repid=rep1&type=pdf (bibliographic record https://repo.uum.edu.my/id/eprint/3494/). The graph motivation is https://arxiv.org/html/2610.22142v1, Section3.3 and the open conjecture in Section6. Incidence square sums and three-element inclusion-exclusion are ordinary finite counting. No novelty, wild-number bound, sharpness case, or research advance is claimed. Exact finite audit8955 is diagnostic, not a hypothesis.

Let n>=3 and let A be a symmetric idempotent row-injective array on Fin n. Index its ordered witnesses by W={(x,y):x!=y}, with support T(x,y)={x,y,A(x,y)}. The number D of ORDERED pairs of witnesses whose supports are disjoint, plus the number Q of ORDERED pairs whose supports are identical, equals n*(n-1)*(n^2-10*n+27), with all arithmetic in the displayed equality interpreted in the integers. This holds for every such full normalized array; it does not assert the required uniform cubic-cost inequality.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem wild_array_witness_filter_card (n : ℕ)
    (P : Fin n × Fin n → Prop) [DecidablePred P] :
    (univ.filter fun p : {p : Fin n × Fin n // p.1 ≠ p.2} => P p.val).card =
      (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ P p).card := by
  classical
  apply card_bij (fun p _ => p.val)
  · intro p hp
    exact mem_filter.mpr ⟨mem_univ _, p.property, (mem_filter.mp hp).2⟩
  · intro p hp q hq heq
    exact Subtype.ext heq
  · intro p hp
    have hp := (mem_filter.mp hp).2
    exact ⟨⟨p,hp.1⟩, mem_filter.mpr ⟨mem_univ _,hp.2⟩, rfl⟩

theorem wild_normalized_array_disjoint_witness_pair_count
    (n : ℕ) (hn : 3 ≤ n) (A : Fin n → Fin n → Fin n)
    (hid : ∀ a, A a a = a)
    (hsym : ∀ a b, A a b = A b a)
    (hinj : ∀ a, Function.Injective (A a)) :
    let W := {p : Fin n × Fin n // p.1 ≠ p.2}
    let T : W → Finset (Fin n) := fun p => {p.val.1,p.val.2,A p.val.1 p.val.2}
    ((univ.filter fun p : W × W => Disjoint (T p.1) (T p.2)).card : ℤ) +
      ((univ.filter fun p : W × W => T p.1 = T p.2).card : ℤ) =
        (n : ℤ) * ((n : ℤ)-1) * ((n : ℤ)^2-10*(n : ℤ)+27) := by
  classical
  dsimp only
  let W := {p : Fin n × Fin n // p.1 ≠ p.2}
  let T : W → Finset (Fin n) := fun p => {p.val.1,p.val.2,A p.val.1 p.val.2}
  change ((univ.filter fun p : W × W => Disjoint (T p.1) (T p.2)).card : ℤ) +
      ((univ.filter fun p : W × W => T p.1 = T p.2).card : ℤ) = _
  have hout (x y : Fin n) (hxy : x ≠ y) : A x y ≠ x ∧ A x y ≠ y := by
    constructor
    · intro h
      exact hxy ((hinj x) (h.trans (hid x).symm)).symm
    · intro h
      exact hxy ((hinj y) ((hsym y x).trans (h.trans (hid y).symm)))
  have hsize : ∀ w : W, (T w).card = 3 := by
    intro w
    have h := hout w.val.1 w.val.2 w.property
    simp [T,card_insert_of_notMem,w.property,h.1,h.2,
      Ne.symm w.property,Ne.symm h.1,Ne.symm h.2]
  have hvertex (a : Fin n) :
      (univ.filter fun w : W => a ∈ T w).card = 3*(n-1) := by
    change (univ.filter fun w : {p : Fin n × Fin n // p.1 ≠ p.2} =>
      a ∈ ({w.val.1,w.val.2,A w.val.1 w.val.2} : Finset (Fin n))).card = _
    calc
      _ = (univ.filter fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))).card :=
        wild_array_witness_filter_card n
          (fun p => a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)))
      _ = _ := wild_normalized_array_vertex_witness_card n A hid hsym hinj a
  have hpair (a b : Fin n) (hab : a ≠ b) :
      (univ.filter fun w : W => a ∈ T w ∧ b ∈ T w).card = 6 := by
    change (univ.filter fun w : {p : Fin n × Fin n // p.1 ≠ p.2} =>
      a ∈ ({w.val.1,w.val.2,A w.val.1 w.val.2} : Finset (Fin n)) ∧
      b ∈ ({w.val.1,w.val.2,A w.val.1 w.val.2} : Finset (Fin n))).card = _
    calc
      _ = (univ.filter fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)) ∧
          b ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))).card :=
        wild_array_witness_filter_card n
          (fun p => a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)) ∧
            b ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)))
      _ = _ := wild_normalized_array_pair_witness_card n A hid hsym hinj a b hab
  have hcount : Fintype.card W = ((univ : Finset (Fin n)).offDiag).card := by
    calc
      _ = (univ.filter fun _ : W => True).card := by simp
      _ = (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ True).card :=
        wild_array_witness_filter_card n (fun _ => True)
      _ = _ := by
        congr 1
        ext p
        simp
  have hcountZ : (Fintype.card W : ℤ) = (n : ℤ)*((n : ℤ)-1) := by
    rw [hcount,wild_finset_offDiag_card_int]
    simp only [card_univ,Fintype.card_fin]
    ring
  have h := wild_three_uniform_disjoint_pair_count T (3*(n-1)) 6 hsize hvertex hpair
  rw [hcountZ] at h
  simp only [Fintype.card_fin] at h
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_mul, Nat.cast_sub hn1] at h
  norm_num at h
  nlinarith [h]
