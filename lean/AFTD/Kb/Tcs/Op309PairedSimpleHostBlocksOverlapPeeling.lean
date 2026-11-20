import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel

/-!
# op309_paired_simple_host_blocks_overlap_peeling

Topic: graphs   Node: fd579b49adff

Provenance: helper lemma. OP-309 independent-centers structural obstruction, IN-1099.

For a simple host edge system in which every edge has a distinct same-class mate, if each host is incident with zero or three classes then overlap-five peeling is impossible.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem in1099_triple_host_core
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) (hS : S.Nonempty)
    (hhost : ∀ b : B, (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 0 ∨
      (S.filter (fun a : A => I.Adj (.inl a) (.inr b))).card = 3)
    (hclass : ∀ a ∈ S, 3 ≤ (Finset.univ.filter (fun b : B => I.Adj (.inl a) (.inr b))).card) :
    ¬ op309_incidence_overlap_five_peel I := by
  intro hpeel
  obtain ⟨a,ha,_,hw⟩ := hpeel S hS
  have hlocal (b : B) : (if I.Adj (.inl a) (.inr b) then
      (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card - 1 else 0) =
      (if I.Adj (.inl a) (.inr b) then 2 else 0) := by
    by_cases hab : I.Adj (.inl a) (.inr b)
    · simp only [hab, if_true]
      have hp : 0 < (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card :=
        Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hab⟩⟩
      rcases hhost b with hzero | hthree <;> omega
    · simp [hab]
  have heq : (∑ b : B, if I.Adj (.inl a) (.inr b) then
        (S.filter (fun a' : A => I.Adj (.inl a') (.inr b))).card - 1 else 0) =
      2 * (Finset.univ.filter (fun b : B => I.Adj (.inl a) (.inr b))).card := by
    simp_rw [hlocal]
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  rw [heq] at hw
  have := hclass a ha
  omega



theorem in1099_two_edges_three_vertices {V : Type*} [DecidableEq V]
    (u v x y : V) (huv : u ≠ v) (hxy : x ≠ y)
    (hne : s(u,v) ≠ s(x,y)) :
    3 ≤ (({u,v} : Finset V) ∪ {x,y}).card := by
  have hthird : x ∉ ({u,v} : Finset V) ∨ y ∉ ({u,v} : Finset V) := by
    by_contra h
    push_neg at h
    have hx : x = u ∨ x = v := by simpa using h.1
    have hy : y = u ∨ y = v := by simpa using h.2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp_all [Sym2.eq_swap]
  rcases hthird with hx | hy
  · have hsub : ({u,v,x} : Finset V) ⊆ ({u,v} : Finset V) ∪ {x,y} := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hz ⊢
      aesop
    have hcard := Finset.card_le_card hsub
    have hxu : x ≠ u := by intro h; subst x; simp at hx
    have hxv : x ≠ v := by intro h; subst x; simp at hx
    have hc : ({u,v,x} : Finset V).card = 3 := by simp [huv,hxu.symm,hxv.symm]
    omega
  · have hsub : ({u,v,y} : Finset V) ⊆ ({u,v} : Finset V) ∪ {x,y} := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hz ⊢
      aesop
    have hcard := Finset.card_le_card hsub
    have hyu : y ≠ u := by intro h; subst y; simp at hy
    have hyv : y ≠ v := by intro h; subst y; simp at hy
    have hc : ({u,v,y} : Finset V).card = 3 := by simp [huv,hyu.symm,hyv.symm]
    omega

theorem op309_paired_simple_host_blocks_overlap_peeling
    {E A B : Type*} [Fintype E] [Nonempty E] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (left right : E → B) (q : E → A)
    (hne : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f → s(left e,right e) ≠ s(left f,right f))
    (hmate : ∀ e, ∃ f, e ≠ f ∧ q f = q e)
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj]
    (hinc : ∀ a b, I.Adj (.inl a) (.inr b) ↔
      ∃ e, q e = a ∧ (left e = b ∨ right e = b))
    (hhost : ∀ b : B,
      ((Finset.univ.image q).filter (fun a => I.Adj (.inl a) (.inr b))).card = 0 ∨
      ((Finset.univ.image q).filter (fun a => I.Adj (.inl a) (.inr b))).card = 3) :
    ¬ op309_incidence_overlap_five_peel I := by
  let S : Finset A := Finset.univ.image q
  have hS : S.Nonempty := by
    obtain ⟨e⟩ := ‹Nonempty E›
    exact ⟨q e, Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩
  apply in1099_triple_host_core I S hS hhost
  intro a ha
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨f,hef,hq⟩ := hmate e
  have hc := in1099_two_edges_three_vertices (left e) (right e) (left f) (right f)
    (hne e) (hne f) (hsimple e f hef)
  apply le_trans hc
  apply Finset.card_le_card
  intro b hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(hinc (q e) b).mpr ?_⟩
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with (rfl | rfl) | (rfl | rfl)
  · exact ⟨e,rfl,Or.inl rfl⟩
  · exact ⟨e,rfl,Or.inr rfl⟩
  · exact ⟨f,hq,Or.inl rfl⟩
  · exact ⟨f,hq,Or.inr rfl⟩
