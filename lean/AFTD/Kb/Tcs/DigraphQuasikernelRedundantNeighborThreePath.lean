import AFTD.Prelude

/-!
# digraph_quasikernel_redundant_neighbor_three_path

Topic: graphs   Node: 7930a9a29a89

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

For an inclusion-minimal quasi-kernel in a source-free loopless digraph, a member whose first out-neighbors are all shared with other members is reached from another member by a directed three-step walk whose penultimate vertex lies outside the quasi-kernel and its first out-neighborhood.
-/

theorem digraph_quasikernel_redundant_neighbor_three_path
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q : Finset α) (q : α)
    (hq : q ∈ Q)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hsource : ∀ v, ∃ u, D.Adj u v)
    (hind : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
    (hmin : ¬ ∀ v, ∃ u ∈ Q.erase q,
        u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
    (hredundant : ∀ b, D.Adj q b → ∃ r ∈ Q.erase q, D.Adj r b) :
    ∃ r ∈ Q.erase q, ∃ b x, D.Adj r b ∧ D.Adj b x ∧ D.Adj x q ∧
       x ∉ Q ∧ (∀ s ∈ Q, ¬ D.Adj s x) := by
  classical
  have hother : ∀ v, v ≠ q → ∃ u ∈ Q.erase q,
      u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v := by
    intro v hv
    obtain ⟨u, hu, hd⟩ := hcover v
    by_cases huq : u = q
    · subst u
      rcases hd with heq | ha | ⟨w, haw, hwv⟩
      · exact (hv heq.symm).elim
      · obtain ⟨r, hr, hrv⟩ := hredundant v ha
        exact ⟨r, hr, Or.inr (Or.inl hrv)⟩
      · obtain ⟨r, hr, hrw⟩ := hredundant w haw
        exact ⟨r, hr, Or.inr (Or.inr ⟨w, hrw, hwv⟩)⟩
    · exact ⟨u, Finset.mem_erase.mpr ⟨huq, hu⟩, hd⟩
  have hqnot : ¬ ∃ u ∈ Q.erase q,
      u = q ∨ D.Adj u q ∨ ∃ w, D.Adj u w ∧ D.Adj w q := by
    intro h
    apply hmin
    intro v
    by_cases hv : v = q
    · simpa [hv] using h
    · exact hother v hv
  obtain ⟨x, hxq⟩ := hsource q
  have hxQ : x ∉ Q := by
    intro hx
    by_cases hxq' : x = q
    · subst x; exact hloop q hxq
    · exact hind x hx q hq hxq' hxq
  have hxfirst : ∀ s ∈ Q, ¬ D.Adj s x := by
    intro s hs hsx
    by_cases hsq : s = q
    · subst s
      obtain ⟨r, hr, hrx⟩ := hredundant x hsx
      exact hqnot ⟨r, hr, Or.inr (Or.inr ⟨x, hrx, hxq⟩)⟩
    · exact hqnot ⟨s, Finset.mem_erase.mpr ⟨hsq, hs⟩,
        Or.inr (Or.inr ⟨x, hsx, hxq⟩)⟩
  obtain ⟨s, hs, hsx⟩ := hcover x
  rcases hsx with heq | ha | ⟨b, hsb, hbx⟩
  · subst s; exact (hxQ hs).elim
  · exact (hxfirst s hs ha).elim
  · by_cases hsq : s = q
    · subst s
      obtain ⟨r, hr, hrb⟩ := hredundant b hsb
      exact ⟨r, hr, b, x, hrb, hbx, hxq, hxQ, hxfirst⟩
    · exact ⟨s, Finset.mem_erase.mpr ⟨hsq, hs⟩, b, x,
        hsb, hbx, hxq, hxQ, hxfirst⟩
