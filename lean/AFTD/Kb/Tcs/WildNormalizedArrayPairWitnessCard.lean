import AFTD.Prelude

/-!
# wild_normalized_array_pair_witness_card

Topic: graphs   Node: 686a6c5475bd

Provenance: helper lemma. IN-359 / OP-306 helper for the uniform weighted-moment route. The associated threefold triple system is standard: Compatible factorizations and three-fold triple systems (2006), construction in the proof of Theorem4.1, https://citeseerx.ist.psu.edu/document?doi=58cc9f2b7c3862f0964a05e0ac1529b9c9de8e5e&repid=rep1&type=pdf (bibliographic record https://repo.uum.edu.my/id/eprint/3494/). The graph motivation is https://arxiv.org/html/2610.22142v1, Section3.3 and the open conjecture in Section6. Incidence square sums and three-element inclusion-exclusion are ordinary finite counting. No novelty, wild-number bound, sharpness case, or research advance is claimed. Exact finite audit8955 is diagnostic, not a hypothesis.

Let A be a symmetric idempotent row-injective array on Fin n. For any two distinct vertices a,b, exactly six ORDERED pairs (x,y), x!=y, have both a and b in the witness support {x,y,A(x,y)}. Opposite orientations are counted separately; this is pair multiplicity three for the unordered witness multiset. Outputs lie in the full Fin n universe.
-/

open Finset
set_option maxHeartbeats 4000000

theorem wild_normalized_array_pair_witness_card
    (n : ℕ) (A : Fin n → Fin n → Fin n)
    (hid : ∀ a, A a a = a)
    (hsym : ∀ a b, A a b = A b a)
    (hinj : ∀ a, Function.Injective (A a))
    (a b : Fin n) (hab : a ≠ b) :
    (univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)) ∧
        b ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))).card = 6 := by
  classical
  obtain ⟨u, hu⟩ := (Finite.surjective_of_injective (hinj a)) b
  obtain ⟨v, hv⟩ := (Finite.surjective_of_injective (hinj b)) a
  have hua : u ≠ a := by
    intro h
    subst u
    rw [hid] at hu
    exact hab hu
  have hub : u ≠ b := by
    intro h
    subst u
    have h : A b a = A b b := by rw [← hsym, hu, hid]
    exact hab ((hinj b) h)
  have hvb : v ≠ b := by
    intro h
    subst v
    rw [hid] at hv
    exact hab hv.symm
  have hva : v ≠ a := by
    intro h
    subst v
    have h : A a b = A a a := by rw [hsym, hv, hid]
    exact hab ((hinj a) h).symm
  have hua' : A u a = b := by rw [hsym, hu]
  have hvb' : A v b = a := by rw [hsym, hv]
  have heq : (univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ a ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n)) ∧
        b ∈ ({p.1,p.2,A p.1 p.2} : Finset (Fin n))) =
      {(a,b),(b,a),(a,u),(u,a),(b,v),(v,b)} := by
    ext p
    rcases p with ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hxy, ha, hb⟩
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with hax | hay | haA
      · subst x
        rcases hb with hba | hby | hbA
        · exact False.elim (hab hba.symm)
        · subst y
          simp
        · have hy : y = u := (hinj a) (hbA.symm.trans hu.symm)
          subst y
          simp
      · subst y
        rcases hb with hbx | hba | hbA
        · subst x
          simp
        · exact False.elim (hab hba.symm)
        · have hx : x = u := (hinj a) ((hsym a x).trans (hbA.symm.trans hu.symm))
          subst x
          simp
      · rcases hb with hbx | hby | hbA
        · subst x
          have hy : y = v := (hinj b) (haA.symm.trans hv.symm)
          subst y
          simp
        · subst y
          have hx : x = v := (hinj b) ((hsym b x).trans (haA.symm.trans hv.symm))
          subst x
          simp
        · exact False.elim (hab (haA.trans hbA.symm))
    · intro hp
      simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hp
      rcases hp with h | h | h | h | h | h
      all_goals rcases h with ⟨rfl,rfl⟩
      all_goals simp [hab, Ne.symm hab, hua, hub, hva, hvb,
        Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb, hu, hv, hua', hvb']
  rw [heq]
  simp [card_insert_of_notMem, Prod.mk.injEq, hab, Ne.symm hab,
    hua, hub, hva, hvb, Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb]
