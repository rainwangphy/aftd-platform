import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphLargeEq
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.PermutationPartialAssignmentCardBoundOfSwitching
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.F

/-!
# wild_number_complete_graph_upper_sub_four_add_parity

Topic: graphs   Node: e54eabdb005a

Provenance: original. Related work: arXiv:2610.22142, Section 3.3.4, Theorem 3.6 and its even-order corollary give n-2 for odd n and n-3 for even n. This strengthens each weak upper bound by one on n>=13. The proof randomly permutes two triples and the remaining n-6 vertices; closure of the remaining block is equivalent to closure of the union of the triples. No equality with the conjectured lower bound is asserted.

For every integer n>=13, every natural number k equal to the chromatic number of the line graph of K_n, and every proper edge coloring c of K_n with color set Fin k, the wild number is at most (n-4)+(n mod 2). This is n-3 for odd n>=13 and n-4 for even n>=14.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {n : ℕ}
open Classical in
lemma w3_assignment_card (D : Finset (Fin n)) (f : Fin n → Fin n)
    (hf : Set.InjOn f (↑D : Set (Fin n))) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ x ∈ D, σ x = f x)).card ≤ (n-D.card).factorial := by
  classical
  have hi := permutation_partial_assignment_card_bound_of_switching D f hf
    (Finset.univ : Finset (Equiv.Perm (Fin n))) (by intro a ha σ hσ hσa y; exact Finset.mem_univ _)
  simp only [Fintype.card_fin, Finset.card_univ, Fintype.card_perm] at hi
  have hd : D.card ≤ n := by simpa using Finset.card_le_univ D
  have he := Nat.factorial_mul_descFactorial hd
  have hp : 0 < (n : ℕ).descFactorial D.card := Nat.descFactorial_pos.2 hd
  apply Nat.le_of_mul_le_mul_left (c := (n : ℕ).descFactorial D.card) (hc := hp)
  convert hi.trans_eq (he.symm.trans (Nat.mul_comm _ _)) using 1
  congr 1
  apply congrArg Finset.card
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
lemma w3_closed_event_card
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
    (D : Finset (Fin n)) (i : Fin n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => w279_closed c i (D.image σ))).card ≤
      D.card.factorial * Nat.choose (n/2) (D.card/2) * (n-D.card).factorial := by
  classical
  let A : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun σ => w279_closed c i (D.image σ)
  let F : Finset (Fin n → Fin n) := Finset.univ.filter fun f =>
    (∀ x ∉ D, f x = x) ∧ Set.InjOn f (↑D : Set (Fin n)) ∧ w279_closed c i (D.image f)
  let φ : Equiv.Perm (Fin n) → Fin n → Fin n := fun σ x => if x ∈ D then σ x else x
  have hmaps : ∀ σ ∈ A, φ σ ∈ F := by
    intro σ hσ
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; simp only [φ, if_neg hx]
    · intro x hx y hy he
      change x ∈ D at hx
      change y ∈ D at hy
      dsimp only [φ] at he
      rw [if_pos hx, if_pos hy] at he
      exact σ.injective he
    · have he : D.image (φ σ) = D.image σ := by
        apply Finset.image_congr
        intro x hx
        change x ∈ D at hx
        simp only [φ, if_pos hx]
      rw [he]
      exact (Finset.mem_filter.1 hσ).2
  have hF : F.card ≤ D.card.factorial * Nat.choose (n/2) (D.card/2) := by
    have hi := w279_count_events D (fun U => w279_closed c i U)
    have hc := w279_count_closed c m hm i D.card
    have hr : (w279_R c m i).card = n/2 := by have := w279_card_R c m hm i; omega
    rw [hr] at hc
    exact hi.trans (Nat.mul_le_mul_left _ hc)
  have hb : A.card ≤ F.card * (n-D.card).factorial := by
    rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := F) hmaps]
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun f hf => ?_
    have hfi := (Finset.mem_filter.1 hf).2.2.1
    refine (Finset.card_le_card ?_).trans (w3_assignment_card D f hfi)
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x hx
    have he := congrFun hσ.2 x
    simpa only [φ, if_pos hx] using he
  exact hb.trans (Nat.mul_le_mul_right _ hF)


lemma w3_mass_polynomial (n : ℕ) (hn : 13 ≤ n) (hodd : n % 2 = 1) :
    n*(12*(n/2)*(n-3).descFactorial 3+120*(n/2)^3) < n.descFactorial 6 := by
  obtain ⟨r,rfl⟩ : ∃ r : ℕ, n=2*r+13 := by exact ⟨(n-13)/2, by omega⟩
  have hm : (2*r+13)/2 = r+6 := by omega
  rw [hm]
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.sub_sub]
  simp only [show 2*r+13-1=2*r+12 by omega, show 2*r+13-2=2*r+11 by omega,
    show 2*r+13-3=2*r+10 by omega, show 2*r+13-4=2*r+9 by omega,
    show 2*r+13-5=2*r+8 by omega]
  have hp : 0 < (2*r+13)*2*(r+6)*(16*r^4+256*r^3+1448*r^2+3140*r+1440) := by positivity
  nlinarith only [hp]

lemma w3_mass_lt (n : ℕ) (hn : 13 ≤ n) (hodd : n % 2 = 1) :
    n*(2*(3 : ℕ).factorial*Nat.choose (n/2) 1*(n-3).factorial+
      (6 : ℕ).factorial*Nat.choose (n/2) 3*(n-6).factorial) < n.factorial := by
  have hc := Nat.descFactorial_le_pow (n/2) 3
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hc
  norm_num only [Nat.factorial_succ, Nat.factorial_zero] at hc
  have h1 := Nat.factorial_mul_descFactorial (n := n) (k := 6) (by omega : 6 ≤ n)
  have h2 := Nat.factorial_mul_descFactorial (n := n-3) (k := 3) (by omega : 3 ≤ n-3)
  simp only [Nat.sub_sub, show 3+3=6 by decide] at h2
  have hp := w3_mass_polynomial n hn hodd
  calc _ ≤ (n-6).factorial * (n*(12*(n/2)*(n-3).descFactorial 3+120*(n/2)^3)) := by
          rw [← h2]
          norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.choose_one_right]
          have hi := Nat.mul_le_mul_left (120*n*(n-6).factorial) hc
          nlinarith only [hi]
    _ < (n-6).factorial * n.descFactorial 6 := Nat.mul_lt_mul_of_pos_left hp (Nat.factorial_pos _)
    _ = _ := h1

def w3_block (v : Fin n) : Fin 3 := if v.val<3 then 0 else if v.val<6 then 1 else 2

def w3_sel (j b : Fin 3) : Prop := if j=0 then b=0 else if j=1 then b=1 else b≠2
instance w3_sel_decidable (j b : Fin 3) : Decidable (w3_sel j b) := by unfold w3_sel; infer_instance

def w3_positions (j : Fin 3) : Finset (Fin n) := Finset.univ.filter fun v => w3_sel j (w3_block v)

lemma w3_mem_positions (j : Fin 3) (v : Fin n) : v ∈ w3_positions j ↔ w3_sel j (w3_block v) := by simp [w3_positions]

lemma w3_positions_card (hn : 7 ≤ n) (j : Fin 3) :
    (w3_positions (n := n) j).card = if j=2 then 6 else 3 := by
  have he0 : w3_positions (n := n) 0 = {⟨0,by omega⟩,⟨1,by omega⟩,⟨2,by omega⟩} := by
    ext v
    simp only [w3_positions, Finset.mem_filter, Finset.mem_univ, true_and, w3_sel, w3_block,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    split_ifs <;> omega
  have he1 : w3_positions (n := n) 1 = {⟨3,by omega⟩,⟨4,by omega⟩,⟨5,by omega⟩} := by
    ext v
    simp only [w3_positions, Finset.mem_filter, Finset.mem_univ, true_and, w3_sel, w3_block,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    split_ifs <;> omega
  have he2 : w3_positions (n := n) 2 = {⟨0,by omega⟩,⟨1,by omega⟩,⟨2,by omega⟩,⟨3,by omega⟩,⟨4,by omega⟩,⟨5,by omega⟩} := by
    ext v
    simp only [w3_positions, Finset.mem_filter, Finset.mem_univ, true_and, w3_sel, w3_block,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    split_ifs <;> omega
  fin_cases j <;> norm_num [he0, he1, he2, Fin.ext_iff]
  change (w3_positions (n := n) 2).card = 6
  rw [he2]
  norm_num [Fin.ext_iff]

lemma w3_root (hn : 7 ≤ n) (j : Fin 3) :
    w3_block (⟨3*j.val, by have := j.isLt; omega⟩ : Fin n) = j := by
  fin_cases j <;> norm_num [w3_block, Fin.ext_iff]

lemma w3_cut_shape : ∀ S : Finset (Fin 3), S.Nonempty → S ≠ Finset.univ →
    ∃ j : Fin 3, (∀ b : Fin 3, b ∈ S ↔ w3_sel j b) ∨
      (∀ b : Fin 3, b ∈ S ↔ ¬w3_sel j b) := by
  decide +kernel

lemma w3_avoid_blocks (hn : 13 ≤ n) (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (j : Fin 3) (i : Fin n), ¬w279_closed c i ((w3_positions j).image σ) := by
  classical
  let Bad : Fin 3 × Fin n → Finset (Equiv.Perm (Fin n)) :=
    fun ji => Finset.univ.filter fun σ => w279_closed c ji.2 ((w3_positions (n := n) ji.1).image σ)
  let B : Finset (Equiv.Perm (Fin n)) := Finset.univ.biUnion Bad
  have hb : B.card ≤ n*(2*(3 : ℕ).factorial*Nat.choose (n/2) 1*(n-3).factorial+
      (6 : ℕ).factorial*Nat.choose (n/2) 3*(n-6).factorial) := by
    refine Finset.card_biUnion_le.trans ?_
    have hi : ∑ ji : Fin 3 × Fin n, (Bad ji).card ≤
        ∑ ji : Fin 3 × Fin n, (w3_positions (n := n) ji.1).card.factorial *
          Nat.choose (n/2) ((w3_positions (n := n) ji.1).card/2) * (n-(w3_positions (n := n) ji.1).card).factorial := by
      exact Finset.sum_le_sum fun ji hji => w3_closed_event_card c m hm (w3_positions (n := n) ji.1) ji.2
    refine hi.trans_eq ?_
    rw [Fintype.sum_prod_type]
    simp only [w3_positions_card (by omega : 7 ≤ n)]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff]
    ring
  have hlt : B.card < (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact hb.trans_lt (w3_mass_lt n hn hodd)
  have hne : B ≠ Finset.univ := by intro he; rw [he] at hlt; exact lt_irrefl _ hlt
  have hex : ∃ σ : Equiv.Perm (Fin n), σ ∉ B := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_of_forall h)
  obtain ⟨σ,hσ⟩ := hex
  refine ⟨σ, ?_⟩
  intro j i hi
  exact hσ (Finset.mem_biUnion.2 ⟨(j,i), Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _,hi⟩⟩)

lemma w3_partition (hn : 13 ≤ n) (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ (p : Fin n → Fin 3) (roots : Fin 3 → Fin n), (∀ t, p (roots t) = t) ∧
      ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin 3)), S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e := by
  classical
  obtain ⟨σ,hσ⟩ := w3_avoid_blocks hn hodd c m hm
  refine ⟨(fun v => w3_block (σ.symm v)), (fun j => σ ⟨3*j.val, by have := j.isLt; omega⟩), ?_, ?_⟩
  · intro j
    simpa only [Equiv.symm_apply_apply] using w3_root (by omega : 7 ≤ n) j
  · intro e S hS hSu
    by_contra hno
    push Not at hno
    obtain ⟨j,hj | hj⟩ := w3_cut_shape S hS hSu
    · apply hσ j (c e)
      intro u hu v huv hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      have hxu := (w3_mem_positions j x).1 hx
      by_contra hv
      have hxS := (hj _).2 hxu
      have hvS : w3_block (σ.symm v) ∉ S := by
        intro hvS
        apply hv
        exact Finset.mem_image.2 ⟨σ.symm v, (w3_mem_positions _ _).2 ((hj _).1 hvS), by simp⟩
      exact hno (σ x) v huv (by simpa using hxS) hvS hc
    · apply hσ j (c e)
      intro u hu v huv hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      have hxu := (w3_mem_positions j x).1 hx
      by_contra hv
      have hxS : w3_block (σ.symm (σ x)) ∉ S := by
        intro hh
        exact (hj _).1 (by simpa using hh) hxu
      have hvS : w3_block (σ.symm v) ∈ S := by
        apply (hj _).2
        intro hvj
        exact hv (Finset.mem_image.2 ⟨σ.symm v, (w3_mem_positions _ _).2 hvj, by simp⟩)
      exact hno v (σ x) (Ne.symm huv) hvS hxS ((w279_c_swap c huv).symm.trans hc)

theorem wild_number_complete_graph_upper_sub_four_add_parity (n k : ℕ) (hn : 13 ≤ n)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c ≤ n-4+n%2 := by
  by_cases hodd : n%2=1
  · obtain ⟨m,hm⟩ := w279_missing_vertex_equiv n k (by omega) hodd hk c
    have hk' : k=n := by simpa using Fintype.card_congr m
    subst k
    obtain ⟨p,roots,hr,hc⟩ := w3_partition hn hodd c m hm
    have hu := simple_graph_wild_number_le_of_block_cut_condition (n := n) (q := 3) (by omega) c p roots hr hc
    omega
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm13 : 13 ≤ m := by omega
    have hmOdd : m%2=1 := by omega
    have hk' : k=m := wsc_even_min_colors (by omega) hmOdd hk c
    subst k
    let cc := wsc_restrict_color c
    obtain ⟨miss,hmiss⟩ := wsc_missing_vertex_equiv_of_le m m (by omega) hmOdd le_rfl cc
    obtain ⟨p,roots,hr,hcuts⟩ := w3_partition hm13 hmOdd cc miss hmiss
    have hc : ∀ (i : Fin m) (S : Finset (Fin 3)), S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin m) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ cc ⟨s(u,v),wild_kn_mem huv⟩ = i := by
      intro i S hS hSu
      obtain ⟨e,he⟩ := wsc_color_used (by omega) cc miss hmiss i
      obtain ⟨u,v,huv,hu,hv,hcol⟩ := hcuts e S hS hSu
      exact ⟨u,v,huv,hu,hv,hcol.trans he⟩
    have hu := wsc_even_upper_of_partition (by omega) c p roots hr hc
    omega
