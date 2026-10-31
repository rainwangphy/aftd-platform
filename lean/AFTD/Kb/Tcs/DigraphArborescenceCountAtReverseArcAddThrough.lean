import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough
import AFTD.Kb.Tcs.DigraphReverseArc
import AFTD.Kb.Tcs.DigraphReverseArcAdj
import AFTD.Kb.Tcs.DigraphArborescenceCountAt
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# digraph_arborescence_count_at_reverse_arc_add_through

Topic: graphs   Node: d5f5b64a9454

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

For a tournament with an arc u → v and any root r, the number of arborescences towards r grows by exactly (through-count of v → u after reversal) minus (through-count of u → v before reversal).
-/

/-- Per-root reversal identity in the general "switch the two arcs on the pair {u,v}" form: if `E` agrees with `D` off the pair `{u,v}` and swaps the two arcs on it, and `D` has the arc `v → u` absent, then the `r`-rooted arborescence counts differ by the through-counts for the swapped arcs. -/
private theorem digraph_arborescence_count_at_reverse_arc_add_through_switch {n : ℕ}
    (D E : Digraph (Fin n)) [DecidableRel D.Adj] [DecidableRel E.Adj]
    (u v r : Fin n) (hne : u ≠ v) (hvu : ¬ D.Adj v u)
    (hE1 : ∀ x y : Fin n, ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) → (E.Adj x y ↔ D.Adj x y))
    (hE2 : E.Adj u v ↔ D.Adj v u) (hE3 : E.Adj v u ↔ D.Adj u v) :
    digraph_arborescence_count_at D r + digraph_arborescence_count_at_through E r v u =
      digraph_arborescence_count_at E r + digraph_arborescence_count_at_through D r u v := by
  set P := Finset.univ.filter (fun p : Fin n → Fin n =>
    p r = r ∧ (∀ w, w ≠ r → D.Adj w (p w)) ∧ ∀ w, p^[n] w = r) with hP
  set P' := Finset.univ.filter (fun p : Fin n → Fin n =>
    p r = r ∧ (∀ w, w ≠ r → E.Adj w (p w)) ∧ ∀ w, p^[n] w = r) with hP'
  have hneuv : ¬ E.Adj u v := fun h => hvu (hE2.mp h)
  have memP : ∀ p, p ∈ P ↔ (p r = r ∧ (∀ w, w ≠ r → D.Adj w (p w)) ∧ ∀ w, p^[n] w = r) := by
    intro p; rw [hP]; simp
  have memP' : ∀ p, p ∈ P' ↔ (p r = r ∧ (∀ w, w ≠ r → E.Adj w (p w)) ∧ ∀ w, p^[n] w = r) := by
    intro p; rw [hP']; simp
  -- an `r`-rooted successor map never sends `v` to `u` in `D` ...
  have keyD : ∀ p, p ∈ P → p v ≠ u := by
    intro p hp hpv
    obtain ⟨hr, hadj, hroot⟩ := (memP p).mp hp
    have hvne : v ≠ r := by
      intro h
      have h1 : p v = v := by simpa [h] using hr
      rw [hpv] at h1
      exact hne h1
    exact hvu (hpv ▸ hadj v hvne)
  -- ... and never sends `u` to `v` in `E`.
  have keyE : ∀ p, p ∈ P' → p u ≠ v := by
    intro p hp hpu
    obtain ⟨hr, hadj, hroot⟩ := (memP' p).mp hp
    have hune : u ≠ r := by
      intro h
      have h1 : p u = u := by simpa [h] using hr
      rw [hpu] at h1
      exact hne h1.symm
    exact hneuv (hpu ▸ hadj u hune)
  -- off the two special arcs the two arborescence conditions agree
  have common : P.filter (fun p => p u ≠ v) = P'.filter (fun p => p v ≠ u) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpu⟩
      obtain ⟨hr, hadj, hroot⟩ := (memP p).mp hp
      exact ⟨(memP' p).mpr ⟨hr, fun w hw =>
        (hE1 w (p w) (by rintro ⟨rfl, h⟩; exact hpu h)
          (by rintro ⟨rfl, h⟩; exact keyD p hp h)).mpr (hadj w hw), hroot⟩, keyD p hp⟩
    · rintro ⟨hp, hpv⟩
      obtain ⟨hr, hadj, hroot⟩ := (memP' p).mp hp
      exact ⟨(memP p).mpr ⟨hr, fun w hw =>
        (hE1 w (p w) (by rintro ⟨rfl, h⟩; exact keyE p hp h)
          (by rintro ⟨rfl, h⟩; exact hpv h)).mp (hadj w hw), hroot⟩, keyE p hp⟩
  have fP : P.filter (fun p => p u ≠ v ∧ p v ≠ u) = P.filter (fun p => p u ≠ v) := by
    apply Finset.filter_congr
    intro p hp
    exact ⟨fun h => h.1, fun h => ⟨h, keyD p hp⟩⟩
  have fP' : P'.filter (fun p => p u ≠ v ∧ p v ≠ u) = P'.filter (fun p => p v ≠ u) := by
    apply Finset.filter_congr
    intro p hp
    exact ⟨fun h => h.2, fun h => ⟨keyE p hp, h⟩⟩
  have cardP : (P.filter (fun p => p u = v)).card + (P.filter (fun p => p u ≠ v)).card = P.card := by
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not (s := P) (p := fun p => p u = v)
  have cardP' : (P'.filter (fun p => p v = u)).card + (P'.filter (fun p => p v ≠ u)).card = P'.card := by
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not (s := P') (p := fun p => p v = u)
  have hcountD : digraph_arborescence_count_at D r = P.card := by rw [hP]; rfl
  have hcountE : digraph_arborescence_count_at E r = P'.card := by rw [hP']; rfl
  have hthruE : digraph_arborescence_count_at_through E r v u =
      (P'.filter (fun p => p v = u)).card := by
    rw [hP']
    unfold digraph_arborescence_count_at_through
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hthruD : digraph_arborescence_count_at_through D r u v =
      (P.filter (fun p => p u = v)).card := by
    rw [hP]
    unfold digraph_arborescence_count_at_through
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hCC : P.filter (fun p => p u ≠ v ∧ p v ≠ u) = P'.filter (fun p => p u ≠ v ∧ p v ≠ u) :=
    fP.trans (common.trans fP'.symm)
  rw [hcountD, hcountE, hthruE, hthruD, ← cardP, ← cardP', ← fP, ← fP', ← hCC]
  omega

/-- Reversing the arc u → v raises the number of arborescences towards a fixed root r exactly by the difference of the two through-arc counts. -/
theorem digraph_arborescence_count_at_reverse_arc_add_through {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hT : digraph_is_tournament D) (u v : Fin n) (huv : D.Adj u v) (r : Fin n) :
    digraph_arborescence_count_at D r +
        digraph_arborescence_count_at_through (digraph_reverse_arc D u v) r v u =
      digraph_arborescence_count_at (digraph_reverse_arc D u v) r +
        digraph_arborescence_count_at_through D r u v := by
  have hne : u ≠ v := fun h => hT.1 v (h ▸ huv)
  have hvu : ¬ D.Adj v u := (hT.2 u v hne).1 huv
  exact digraph_arborescence_count_at_reverse_arc_add_through_switch D (digraph_reverse_arc D u v)
    u v r hne hvu (digraph_reverse_arc_adj D u v).1 (digraph_reverse_arc_adj D u v).2.1
    (digraph_reverse_arc_adj D u v).2.2
