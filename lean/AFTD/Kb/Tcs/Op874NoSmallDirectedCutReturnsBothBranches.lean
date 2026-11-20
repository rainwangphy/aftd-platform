import AFTD.Prelude

/-!
# op874_no_small_directed_cut_returns_both_branches

Topic: graphs   Node: 1a5fe89ef9ad

Provenance: helper lemma. Rooted branch reachability from absence of a one-arc outgoing cut.

In a finite two-in/two-out directed multigraph with at least two outgoing arcs from every nonempty proper vertex set, for every root and each successor x, both arcs leaving x lead back to the root without passing through x.
-/

theorem op874_no_small_directed_cut_returns_both_branches {X : Type*} [Fintype X] [DecidableEq X] (p q : Equiv.Perm X) (hfixed : ∀ x, p x ≠ x ∧ q x ≠ x) (hcut : ∀ S : Finset X, S.Nonempty → S ≠ Finset.univ → ∃ a b : X × Bool, a ≠ b ∧ a.1 ∈ S ∧ b.1 ∈ S ∧ (if a.2 then p a.1 else q a.1) ∉ S ∧ (if b.2 then p b.1 else q b.1) ∉ S) (r x : X) (harc : p r = x ∨ q r = x) : Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (p x) r ∧ Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (q x) r := by
  classical
  let R : X → X → Prop := fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)
  have hrx : r ≠ x := by
    rcases harc with hp | hq
    · intro heq; exact (hfixed r).1 (hp.trans heq.symm)
    · intro heq; exact (hfixed r).2 (hq.trans heq.symm)
  let S : Finset X := Finset.univ.filter (fun u => u ≠ x ∧ ¬ Relation.ReflTransGen R u r)
  have hmem (u : X) : u ∈ S ↔ u ≠ x ∧ ¬ Relation.ReflTransGen R u r := by simp [S]
  have hr : r ∉ S := by
    intro h
    exact ((hmem r).mp h).2 Relation.ReflTransGen.refl
  have hclosure (u v : X) (hu : u ∈ S) (hv : v ≠ x) (huv : p u = v ∨ q u = v) : v ∈ S := by
    rw [hmem] at hu ⊢
    refine ⟨hv, ?_⟩
    intro hvR
    exact hu.2 (Relation.ReflTransGen.head ⟨hu.1, hv, huv⟩ hvR)
  have hempty : S = ∅ := by
    by_contra hs
    have hn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    have hp : S ≠ Finset.univ := by intro h; exact hr (h ▸ Finset.mem_univ r)
    obtain ⟨⟨u, bu⟩, ⟨v, bv⟩, huv, hu, hv, hou, hov⟩ := hcut S hn hp
    simp only at hu hv hou hov
    have hut : (if bu then p u else q u) = x := by
      by_contra hn
      apply hou
      apply hclosure u _ hu hn
      cases bu <;> simp
    have hvt : (if bv then p v else q v) = x := by
      by_contra hn
      apply hov
      apply hclosure v _ hv hn
      cases bv <;> simp
    rcases harc with hrp | hrq
    · cases bu <;> cases bv <;> simp only [Bool.false_eq_true, ↓reduceIte] at hut hvt
      · exact huv (congrArg (fun z => (z, false)) (q.injective (hut.trans hvt.symm)))
      · have : v = r := p.injective (hvt.trans hrp.symm)
        subst v; exact hr hv
      · have : u = r := p.injective (hut.trans hrp.symm)
        subst u; exact hr hu
      · have : u = r := p.injective (hut.trans hrp.symm)
        subst u; exact hr hu
    · cases bu <;> cases bv <;> simp only [Bool.false_eq_true, ↓reduceIte] at hut hvt
      · have : u = r := q.injective (hut.trans hrq.symm)
        subst u; exact hr hu
      · have : u = r := q.injective (hut.trans hrq.symm)
        subst u; exact hr hu
      · have : v = r := q.injective (hvt.trans hrq.symm)
        subst v; exact hr hv
      · exact huv (congrArg (fun z => (z, true)) (p.injective (hut.trans hvt.symm)))
  constructor
  · by_contra h; have : p x ∈ S := (hmem _).2 ⟨(hfixed x).1, h⟩; simp [hempty] at this
  · by_contra h; have : q x ∈ S := (hmem _).2 ⟨(hfixed x).2, h⟩; simp [hempty] at this
