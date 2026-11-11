import AFTD.Prelude
import AFTD.Kb.Tcs.Op869AdversaryForces
import AFTD.Kb.Tcs.Op869PredecessorCausality
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.ColorsUsed

/-!
# op869_adversary_forces_sound

Topic: online_algorithms   Node: 96c7b5d49e55

Provenance: helper lemma. arXiv:2610.41516, Sections 1 and 2; formal infrastructure for the adaptive online-coloring construction.

A winning one-fold adversary position, whose recorded earlier colors agree with a proper online algorithm on the current predecessor graph, gives a k-colorable graph on which that algorithm uses at least K colors.
-/

theorem op869_adversary_forces_sound {n : ℕ} (k K : ℕ)
    (A : SimpleGraph (Fin n) → Fin n → ℕ)
    (hA : IsOnlineColoringAlg A) (hproper : ProperlyColorsKColorable k A)
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (hplay : op869_adversary_forces k 1 K fuel i P C)
    (hinv : ∀ a : Fin n, a.val < i → C a = {A (op869_graph_from_predecessors P) a}) :
    ∃ G : SimpleGraph (Fin n), G.Colorable k ∧ K ≤ colorsUsed (A G) := by
  induction fuel generalizing i P C with
  | zero => simp [op869_adversary_forces] at hplay
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_adversary_forces, dif_pos hi] at hplay
      obtain ⟨S, hS, hcolor, hnext⟩ := hplay
      let v : Fin n := ⟨i, hi⟩
      let P' := Function.update P v S
      let G := op869_graph_from_predecessors P'
      have hbefore (a : Fin n) (ha : a.val < i) : C a = {A G a} := by
        rw [hinv a ha]
        congr 1
        apply op869_predecessor_causality A hA P P' a
        intro j hj
        have hj' : j.val ≤ a.val := hj
        have hjne : j ≠ v := by
          intro h
          have heq : j.val = i := congrArg Fin.val h
          omega
        simp [P', hjne, Ne.symm hjne]
      let c : Finset ℕ := {A G v}
      have hc : ∀ a ∈ S, Disjoint (C a) c := by
        intro a ha
        have hlt : a < v := hS a ha
        have hadj : G.Adj a v := by
          exact Or.inl ⟨hlt, by simp [G, P', op869_graph_from_predecessors, ha]⟩
        rw [hbefore a (hS a ha)]
        exact Finset.disjoint_singleton.mpr (hproper G hcolor a v hadj)
      let C' := Function.update C v c
      have hprefix (a : Fin n) (ha : a.val ≤ i) : C' a = {A G a} := by
        rcases lt_or_eq_of_le ha with ha | ha
        · have hne : a ≠ v := by
            intro h
            have heq : a.val = i := congrArg Fin.val h
            omega
          simpa [C', hne, Ne.symm hne] using hbefore a ha
        · have heq : a = v := Fin.ext ha
          subst a
          simp [C', c]
      rcases hnext c (by simp [c]) hc with hK | hgame
      · refine ⟨G, hcolor, ?_⟩
        apply le_trans hK
        unfold colorsUsed
        apply Finset.card_le_card
        intro x hx
        obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
        have ha' : a.val ≤ i := (Finset.mem_filter.mp ha).2
        change x ∈ C' a at hx
        rw [hprefix a ha'] at hx
        have heq : x = A G a := Finset.mem_singleton.mp hx
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq.symm⟩
      · apply ih (i + 1) P' C' hgame
        intro a ha
        exact hprefix a (by omega)
    · simp [op869_adversary_forces, hi] at hplay
