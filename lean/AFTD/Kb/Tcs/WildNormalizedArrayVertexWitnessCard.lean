import AFTD.Prelude

/-!
# wild_normalized_array_vertex_witness_card

Topic: graphs   Node: 0d887818b633

Provenance: helper lemma. IN-359 / OP-306 helper for the uniform weighted-moment route. The associated threefold triple system is standard: Compatible factorizations and three-fold triple systems (2006), construction in the proof of Theorem4.1, https://citeseerx.ist.psu.edu/document?doi=58cc9f2b7c3862f0964a05e0ac1529b9c9de8e5e&repid=rep1&type=pdf (bibliographic record https://repo.uum.edu.my/id/eprint/3494/). The graph motivation is https://arxiv.org/html/2610.22142v1, Section3.3 and the open conjecture in Section6. Incidence square sums and three-element inclusion-exclusion are ordinary finite counting. No novelty, wild-number bound, sharpness case, or research advance is claimed. Exact finite audit8955 is diagnostic, not a hypothesis.

Let A be a symmetric idempotent row-injective array on Fin n. For any fixed vertex a, exactly3*(n-1) ORDERED pairs (x,y), x!=y, have a in {x,y,A(x,y)}. These split into the two endpoint roles and the output role. This is an incidence identity, not a partition or seal-avoidance theorem.
-/

open Finset
set_option maxHeartbeats 4000000

theorem wild_normalized_array_vertex_witness_card
    (n : ℕ) (A : Fin n → Fin n → Fin n)
    (hid : ∀ a, A a a = a)
    (hsym : ∀ a b, A a b = A b a)
    (hinj : ∀ a, Function.Injective (A a))
    (a : Fin n) :
    (univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))).card =
      3 * (n-1) := by
  classical
  have hout (x y : Fin n) (hxy : x ≠ y) : A x y ≠ x ∧ A x y ≠ y := by
    constructor
    · intro h
      have heq : A x y = A x x := h.trans (hid x).symm
      exact hxy ((hinj x) heq).symm
    · intro h
      have heq : A y x = A y y := (hsym y x).trans (h.trans (hid y).symm)
      exact hxy ((hinj y) heq)
  let X : Finset (Fin n × Fin n) := univ.filter fun p => p.1 ≠ p.2 ∧ a = p.1
  let Y : Finset (Fin n × Fin n) := univ.filter fun p => p.1 ≠ p.2 ∧ a = p.2
  let Z : Finset (Fin n × Fin n) := univ.filter fun p => p.1 ≠ p.2 ∧ a = A p.1 p.2
  have hX : X.card = n-1 := by
    have h : X.card = (univ.erase a).card := by
      apply card_bij (fun p _ => p.2)
      · intro p hp
        have hp := (mem_filter.mp hp).2
        exact mem_erase.mpr ⟨fun h => hp.1 (hp.2.symm.trans h.symm), mem_univ _⟩
      · intro p hp q hq he
        have hp := (mem_filter.mp hp).2
        have hq := (mem_filter.mp hq).2
        exact Prod.ext (hp.2.symm.trans hq.2) he
      · intro y hy
        refine ⟨(a,y), ?_, rfl⟩
        exact mem_filter.mpr ⟨mem_univ _, Ne.symm (mem_erase.mp hy).1, rfl⟩
    simpa using h
  have hY : Y.card = n-1 := by
    have h : Y.card = (univ.erase a).card := by
      apply card_bij (fun p _ => p.1)
      · intro p hp
        have hp := (mem_filter.mp hp).2
        exact mem_erase.mpr ⟨fun h => hp.1 (h.trans hp.2), mem_univ _⟩
      · intro p hp q hq he
        have hp := (mem_filter.mp hp).2
        have hq := (mem_filter.mp hq).2
        exact Prod.ext he (hp.2.symm.trans hq.2)
      · intro x hx
        refine ⟨(x,a), ?_, rfl⟩
        exact mem_filter.mpr ⟨mem_univ _, (mem_erase.mp hx).1, rfl⟩
    simpa using h
  have hZ : Z.card = n-1 := by
    have h : Z.card = (univ.erase a).card := by
      apply card_bij (fun p _ => p.1)
      · intro p hp
        have hp := (mem_filter.mp hp).2
        exact mem_erase.mpr ⟨fun h => (hout p.1 p.2 hp.1).1 (hp.2.symm.trans h.symm),
          mem_univ _⟩
      · intro p hp q hq he
        have hp := (mem_filter.mp hp).2
        have hq := (mem_filter.mp hq).2
        apply Prod.ext he
        apply hinj p.1
        exact hp.2.symm.trans (hq.2.trans (congrArg (fun x => A x q.2) he.symm))
      · intro x hx
        obtain ⟨y, hy⟩ := (Finite.surjective_of_injective (hinj x)) a
        have hxy : x ≠ y := by
          intro h
          subst y
          rw [hid] at hy
          exact (mem_erase.mp hx).1 hy
        exact ⟨(x,y), mem_filter.mpr ⟨mem_univ _, hxy, hy.symm⟩, rfl⟩
    simpa using h
  have hXY : Disjoint X Y := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp := (mem_filter.mp hp).2
    have hq := (mem_filter.mp hq).2
    exact hp.1 (hp.2.symm.trans hq.2)
  have hXZ : Disjoint X Z := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp := (mem_filter.mp hp).2
    have hq := (mem_filter.mp hq).2
    exact (hout p.1 p.2 hp.1).1 (hq.2.symm.trans hp.2)
  have hYZ : Disjoint Y Z := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp := (mem_filter.mp hp).2
    have hq := (mem_filter.mp hq).2
    exact (hout p.1 p.2 hp.1).2 (hq.2.symm.trans hp.2)
  have heq : (univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))) = X ∪ Y ∪ Z := by
    ext p
    simp only [X, Y, Z, mem_filter, mem_univ, true_and, mem_union,
      mem_insert, mem_singleton]
    tauto
  rw [heq, card_union_of_disjoint (disjoint_union_left.mpr ⟨hXZ,hYZ⟩),
    card_union_of_disjoint hXY, hX, hY, hZ]
  omega
