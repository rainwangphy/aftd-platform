import AFTD.Prelude
import AFTD.Kb.Tcs.Op309CommonHostGraph

/-!
# op309_linear_three_hosts_local_degree_six

Topic: graphs   Node: ac79898dcabc

Provenance: helper lemma. OP-309 canonical port-graph selection; local form of the staged op309_linear_triple_incidence_common_graph_six_regular in state/campaigns/op309-in1166-seeds/six-regular-core-spec.json.

In a finite host-incidence structure, a class incident with exactly three three-class hosts has degree six in the common-host graph if it and every other class share at most one host.
-/

theorem op309_linear_three_hosts_local_degree_six
  {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (a : A)
  (hclass : (Finset.univ.filter fun b : B => I.Adj (.inl a) (.inr b)).card = 3)
  (hhost : ∀ b : B, I.Adj (.inl a) (.inr b) →
    (Finset.univ.filter fun x : A => I.Adj (.inl x) (.inr b)).card = 3)
  (hlinear : ∀ a' : A, a ≠ a' →
    (Finset.univ.filter fun b : B => I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)).card ≤ 1)
  (Q : SimpleGraph A) [DecidableRel Q.Adj] (hQ : Q = op309_common_host_graph I) :
  Q.degree a = 6 := by
  classical
  have hN : Q.neighborFinset a = (Finset.univ.filter fun b : B => I.Adj (.inl a) (.inr b)).biUnion
      (fun b => (Finset.univ.filter fun x : A => I.Adj (.inl x) (.inr b)).erase a) := by
    ext a'
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_biUnion, hQ]
    constructor
    · rintro ⟨hne, b, h1, h2⟩
      exact ⟨b, by simp [h1], by simp [h2, Ne.symm hne]⟩
    · rintro ⟨b, hb, hc⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hb hc
      exact ⟨Ne.symm hc.1, b, hb, hc.2⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hN, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · rw [Finset.sum_const, hclass]; rfl
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.card_erase_of_mem (by simp [hb]), hhost b hb]
  · intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_coe] at hx hx' hb hb'
    have hsub : ({b, b'} : Finset B) ⊆
        Finset.univ.filter fun c : B => I.Adj (.inl a) (.inr c) ∧ I.Adj (.inl x) (.inr c) := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [hb, hx.2]
      · simp [hb', hx'.2]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2
    have := hlinear x (Ne.symm hx.1)
    omega
