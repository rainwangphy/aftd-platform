import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelOutneighbors

/-!
# digraph_quasikernel_outneighbors_two_dominate

Topic: graphs   Node: 8b53dd005adf

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

In a finite loopless source-free digraph, the out-neighborhood of an independent two-step out-dominating set is itself two-step out-dominating.
-/

theorem digraph_quasikernel_outneighbors_two_dominate
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q : Finset α)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hsource : ∀ v, ∃ u, D.Adj u v)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) :
    ∀ v, ∃ b ∈ digraph_quasikernel_outneighbors D Q,
      b = v ∨ D.Adj b v ∨ ∃ w, D.Adj b w ∧ D.Adj w v := by
  classical
  have hmem : ∀ {v}, v ∈ digraph_quasikernel_outneighbors D Q ↔ ∃ q ∈ Q, D.Adj q v := by
    intro v; simp [digraph_quasikernel_outneighbors]
  have houtside : ∀ y, y ∉ Q → y ∈ digraph_quasikernel_outneighbors D Q ∨
      ∃ b ∈ digraph_quasikernel_outneighbors D Q, D.Adj b y := by
    intro y hy
    obtain ⟨q,hq,hd⟩ := hcover y
    rcases hd with heq | ha | ⟨b,hqb,hby⟩
    · subst q; exact (hy hq).elim
    · exact Or.inl (hmem.mpr ⟨q,hq,ha⟩)
    · exact Or.inr ⟨b,hmem.mpr ⟨q,hq,hqb⟩,hby⟩
  intro v
  by_cases hv : v ∈ Q
  · obtain ⟨p,hpv⟩ := hsource v
    have hpQ : p ∉ Q := by
      intro hp
      by_cases hpv' : p = v
      · subst p; exact hloop v hpv
      · exact hind p hp v hv hpv' hpv
    rcases houtside p hpQ with hpB | ⟨b,hb,hbp⟩
    · exact ⟨p,hpB,Or.inr (Or.inl hpv)⟩
    · exact ⟨b,hb,Or.inr (Or.inr ⟨p,hbp,hpv⟩)⟩
  · rcases houtside v hv with hvB | ⟨b,hb,hbv⟩
    · exact ⟨v,hvB,Or.inl rfl⟩
    · exact ⟨b,hb,Or.inr (Or.inl hbv)⟩
