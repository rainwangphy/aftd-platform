import AFTD.Prelude

/-!
# critical_four_two_choice_pairing_counterexample

Topic: fair_division   Node: 171058f07803

Provenance: original. Related work: A counterexample to the two-good-pairs construction for OP-1112, related to arXiv:2609.35280.

There exist four sets L_i, one for each i in Fin 4, of four low chores drawn from the nine chores Fin 9, with the following properties. For every extra chore e and every permutation p of the nine chores which fixes e, has no other fixed points and satisfies p(p(g)) = g for every chore g, there is an agent i such that at most one representative g with g < p(g) satisfies: if e is in L_i, at least one of g and p(g) is in L_i, while if e is not in L_i, both g and p(g) are in L_i. Moreover there is a function F from Fin 4 times Fin 9 to Fin 4 such that for each chore g, t maps to F(t,g) bijectively; for each t and i, exactly three chores g have F(t,g)=i when i=t, and exactly two have F(t,g)=i when i differs from t; and for each t, at most one chore assigned by F(t,−) to t is outside L_t.
-/

open Finset

private lemma critical_pairing_even_card {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → α) (hp : ∀ x ∈ s, p x ∈ s) (hinv : ∀ x ∈ s, p (p x) = x)
    (hfix : ∀ x ∈ s, p x ≠ x) : Even s.card := by
  have hsum : ∑ x ∈ s, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun x _ => p x)
    · intro x hx
      change (1 : ZMod 2) + 1 = 0
      decide
    · intro x hx _
      exact hfix x hx
    · intro x hx
      exact hp x hx
    · intro x hx
      exact hinv x hx
  have hz : (s.card : ZMod 2) = 0 := by simpa using hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hz

private lemma critical_four_lows_closed (L : Finset (Fin 9)) (hL : L.card = 4)
    (p : Equiv.Perm (Fin 9)) (hinv : ∀ x, p (p x) = x)
    (hgood : 2 ≤ (Finset.univ.filter (fun g => g < p g ∧ g ∈ L ∧ p g ∈ L)).card) :
    ∀ x ∈ L, p x ∈ L := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun g => g < p g ∧ g ∈ L ∧ p g ∈ L)).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have haa : a ≠ p a := ne_of_lt ha.1
  have hbb : b ≠ p b := ne_of_lt hb.1
  have hapb : a ≠ p b := by
    intro he
    have hpa : p a = b := by rw [he, hinv]
    have h1 : a < b := by simpa [hpa] using ha.1
    have h2 : b < a := by simpa [he] using hb.1
    exact (lt_asymm h1) h2
  have hpab : p a ≠ b := by
    intro he
    have hpb : p b = a := by rw [← he, hinv]
    have h1 : a < b := by simpa [he] using ha.1
    have h2 : b < a := by simpa [hpb] using hb.1
    exact (lt_asymm h1) h2
  have hpab' : p a ≠ p b := fun h => hab (p.injective h)
  let Q : Finset (Fin 9) := {a,p a,b,p b}
  have hQcard : Q.card = 4 := by
    simp [Q, haa, hbb, hab, hapb, hpab, hpab', Ne.symm haa,
      Ne.symm hbb, Ne.symm hab, Ne.symm hapb, Ne.symm hpab, Ne.symm hpab']
  have hQsub : Q ⊆ L := by
    intro x hx
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha.2.1
    · exact ha.2.2
    · exact hb.2.1
    · exact hb.2.2
  have hQeq : Q = L := Finset.eq_of_subset_of_card_le hQsub (by omega)
  intro x hx
  have hxQ : x ∈ Q := by rw [hQeq]; exact hx
  simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hxQ
  rcases hxQ with rfl | rfl | rfl | rfl
  · exact ha.2.2
  · simpa [hinv a] using ha.2.1
  · exact hb.2.2
  · simpa [hinv b] using hb.2.1
private def critical_four_lows : Fin 4 → Finset (Fin 9) := ![
  {0,5,6,7}, {0,1,2,3}, {1,2,3,4}, {4,5,6,7}]

private def critical_four_allocations : Fin 4 → Fin 9 → Fin 4 := ![
  ![0,3,3,1,1,0,0,2,2],
  ![1,1,1,0,0,2,2,3,3],
  ![2,2,2,3,3,1,1,0,0],
  ![3,0,0,2,2,3,3,1,1]]

private theorem critical_four_odd_overlap_cert :
    (∀ i, (critical_four_lows i).card = 4) ∧
    ∀ e : Fin 9, ∃ i j : Fin 4, e ∉ critical_four_lows i ∧ e ∉ critical_four_lows j ∧
      Odd ((critical_four_lows i ∩ critical_four_lows j).card) := by
  decide

private theorem critical_four_valid_allocation_cert :
    (∀ g : Fin 9, Function.Bijective (fun t => critical_four_allocations t g)) ∧
    (∀ t i : Fin 4, ((Finset.univ.filter (fun g => critical_four_allocations t g = i))).card =
      if i = t then 3 else 2) ∧
    ∀ t : Fin 4, ((Finset.univ.filter (fun g => critical_four_allocations t g = t)) \ critical_four_lows t).card ≤ 1 := by
  decide

private theorem critical_four_no_two_good_pairs_cert :
    ∀ (e : Fin 9) (p : Equiv.Perm (Fin 9)), p e = e →
      (∀ g, g ≠ e → p g ≠ g) → (∀ g, p (p g) = g) →
      ∃ i : Fin 4, (Finset.univ.filter (fun g => g < p g ∧
        if e ∈ critical_four_lows i then g ∈ critical_four_lows i ∨ p g ∈ critical_four_lows i
        else g ∈ critical_four_lows i ∧ p g ∈ critical_four_lows i)).card ≤ 1 := by
  classical
  intro e p he hfix hinv
  by_contra h
  push_neg at h
  obtain ⟨i,j,hei,hej,hodd⟩ := critical_four_odd_overlap_cert.2 e
  have hi : 2 ≤ (Finset.univ.filter (fun g => g < p g ∧ g ∈ critical_four_lows i ∧ p g ∈ critical_four_lows i)).card := by
    have hh := h i
    simp only [hei, ↓reduceIte] at hh
    omega
  have hj : 2 ≤ (Finset.univ.filter (fun g => g < p g ∧ g ∈ critical_four_lows j ∧ p g ∈ critical_four_lows j)).card := by
    have hh := h j
    simp only [hej, ↓reduceIte] at hh
    omega
  have hci := critical_four_lows_closed (critical_four_lows i) (critical_four_odd_overlap_cert.1 i) p hinv hi
  have hcj := critical_four_lows_closed (critical_four_lows j) (critical_four_odd_overlap_cert.1 j) p hinv hj
  have heven : Even ((critical_four_lows i ∩ critical_four_lows j).card) := by
    apply critical_pairing_even_card (critical_four_lows i ∩ critical_four_lows j) p
    · intro x hx
      exact Finset.mem_inter.mpr ⟨hci x (Finset.mem_inter.mp hx).1, hcj x (Finset.mem_inter.mp hx).2⟩
    · intro x hx
      exact hinv x
    · intro x hx
      apply hfix
      intro hxe
      subst x
      exact hei (Finset.mem_inter.mp hx).1
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem critical_four_two_choice_pairing_counterexample :
    ∃ L : Fin 4 → Finset (Fin 9), (∀ i, (L i).card = 4) ∧
      (∀ (e : Fin 9) (p : Equiv.Perm (Fin 9)), p e = e →
        (∀ g, g ≠ e → p g ≠ g) → (∀ g, p (p g) = g) →
        ∃ i : Fin 4, (Finset.univ.filter (fun g => g < p g ∧
          if e ∈ L i then g ∈ L i ∨ p g ∈ L i
          else g ∈ L i ∧ p g ∈ L i)).card ≤ 1) ∧
      ∃ F : Fin 4 → Fin 9 → Fin 4,
        (∀ g, Function.Bijective (fun t => F t g)) ∧
        (∀ t i, (Finset.univ.filter (fun g => F t g = i)).card = if i = t then 3 else 2) ∧
        ∀ t, ((Finset.univ.filter (fun g => F t g = t)) \ L t).card ≤ 1 := by
  refine ⟨critical_four_lows, critical_four_odd_overlap_cert.1,
    critical_four_no_two_good_pairs_cert, critical_four_allocations,
    critical_four_valid_allocation_cert⟩
