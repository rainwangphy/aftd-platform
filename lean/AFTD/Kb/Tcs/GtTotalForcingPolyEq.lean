import AFTD.Prelude
import AFTD.Kb.Tcs.GtGraph
import AFTD.Kb.Tcs.TotalForcingPoly
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.IsTotalForcingSet
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.GtVertex
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.GtAdj

/-!
# gt_total_forcing_poly_eq

Topic: graphs   Node: 4aaeec9d75cf

Provenance: helper lemma. arXiv:2611.11352 Corollary 2

For every integer t ≥ 24, the total forcing polynomial of gt_graph t is equal to the zero forcing polynomial of gt_graph t.
-/

private lemma gt_total_forcing_poly_eq_stuck_notMem {V : Type*} {G : SimpleGraph V} {S W : Set V}
    (hSW : ∀ v, v ∈ S → v ∉ W)
    (hW : ∀ u, u ∉ W → ∀ w, w ∈ W → G.Adj u w → ∃ x, x ∈ W ∧ G.Adj u x ∧ x ≠ w) :
    ∀ v, v ∈ W → ¬ ZeroForced G S v := by
  have key : ∀ v, ZeroForced G S v → v ∈ W → False := by
    intro v hzf
    induction hzf with
    | init v hvS => intro hvW; exact hSW v hvS hvW
    | step u w hu hadj hstep ihu ihstep =>
        intro hwW
        by_cases huw : u ∈ W
        · exact ihu huw
        · obtain ⟨x, hxW, hxadj, hxne⟩ := hW u huw w hwW hadj
          exact ihstep x hxadj hxne hxW
  intro v hvW hzf
  exact key v hzf hvW

private lemma gt_total_forcing_poly_eq_adj_to_R {t : ℕ} (i : Fin t) {u : GtVertex t}
    (hu : u ≠ GtVertex.R i) : (gt_graph t).Adj u (GtVertex.R i) := by
  cases u with
  | A i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | B i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | C i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | D i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | P i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | Q i' => simp [gt_graph, SimpleGraph.fromRel, gt_adj]
  | R i' =>
      have hne : i' ≠ i := fun h => hu (by rw [h])
      simp [gt_graph, SimpleGraph.fromRel, gt_adj, hne, Ne.symm hne]

private lemma gt_total_forcing_poly_eq_R_ne_R {t : ℕ} {i j : Fin t} (h : i ≠ j) :
    (GtVertex.R i) ≠ (GtVertex.R j) := by
  intro hh; exact h (GtVertex.R.inj hh)

private lemma gt_total_forcing_poly_eq_two_neighbors (t : ℕ) (v : GtVertex t) :
    ∃ a b, a ≠ b ∧ (gt_graph t).Adj v a ∧ (gt_graph t).Adj v b := by
  cases v with
  | A i => exact ⟨GtVertex.B 0, GtVertex.B 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | B i => exact ⟨GtVertex.A 0, GtVertex.A 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | C i => exact ⟨GtVertex.B 0, GtVertex.B 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | D i => exact ⟨GtVertex.C 0, GtVertex.C 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | P i => exact ⟨GtVertex.B 0, GtVertex.B 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | Q i => exact ⟨GtVertex.B 0, GtVertex.B 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩
  | R i => exact ⟨GtVertex.B 0, GtVertex.B 1, by simp, by simp [gt_graph, SimpleGraph.fromRel, gt_adj], by simp [gt_graph, SimpleGraph.fromRel, gt_adj]⟩

private lemma gt_total_forcing_poly_eq_exists_R (t : ℕ) (ht : 24 ≤ t) {S : Set (GtVertex t)}
    (hS : is_zero_forcing_set (gt_graph t) S) : ∃ i : Fin t, GtVertex.R i ∈ S := by
  by_contra h
  push Not at h
  set W : Set (GtVertex t) := Set.range GtVertex.R with hWdef
  have hSW : ∀ v, v ∈ S → v ∉ W := by
    intro v hvS hvW
    obtain ⟨i, hi⟩ := hvW
    exact h i (hi ▸ hvS)
  have hstuck : ∀ u, u ∉ W → ∀ w, w ∈ W → (gt_graph t).Adj u w →
      ∃ x, x ∈ W ∧ (gt_graph t).Adj u x ∧ x ≠ w := by
    intro u huW w hwW _
    obtain ⟨i, rfl⟩ := hwW
    have hcardt : 1 < Fintype.card (Fin t) := by rw [Fintype.card_fin]; omega
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcardt i
    have hune : u ≠ GtVertex.R j := fun hh => huW (hh ▸ Set.mem_range_self j)
    exact ⟨GtVertex.R j, Set.mem_range_self j,
      gt_total_forcing_poly_eq_adj_to_R j hune, gt_total_forcing_poly_eq_R_ne_R hji⟩
  have hnotmem := gt_total_forcing_poly_eq_stuck_notMem hSW hstuck
  have hmem : (GtVertex.R (⟨0, by omega⟩ : Fin t)) ∈ W := Set.mem_range_self _
  exact hnotmem _ hmem (hS _)

private lemma gt_total_forcing_poly_eq_card_two_le {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {G : SimpleGraph V}
    (hdeg : ∀ v, ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b)
    {S : Finset V} (hS : is_zero_forcing_set G (S : Set V)) : 2 ≤ S.card := by
  by_contra h
  push Not at h
  have hcle : S.card ≤ 1 := by omega
  have hpair : ∀ a ∈ S, ∀ b ∈ S, a = b := Finset.card_le_one.mp hcle
  have hSW : ∀ v, v ∈ (S : Set V) → v ∉ ((S : Set V)ᶜ) := by
    intro v hv hv'
    exact hv' hv
  have hstuck : ∀ u, u ∉ ((S : Set V)ᶜ) → ∀ w, w ∈ ((S : Set V)ᶜ) → G.Adj u w →
      ∃ x, x ∈ ((S : Set V)ᶜ) ∧ G.Adj u x ∧ x ≠ w := by
    intro u hu w _ hadj
    have huS : u ∈ S := by simpa using hu
    obtain ⟨a, b, hab, hua, hub⟩ := hdeg u
    have haS : a ∉ S := fun ha => (G.ne_of_adj hua) (hpair a ha u huS).symm
    have hbS : b ∉ S := fun hb => (G.ne_of_adj hub) (hpair b hb u huS).symm
    by_cases haw : a = w
    · exact ⟨b, by simpa using hbS, hub, by rw [← haw]; exact hab.symm⟩
    · exact ⟨a, by simpa using haS, hua, haw⟩
  have hWne : ∃ w, w ∈ ((S : Set V)ᶜ) := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    by_cases hv : v ∈ (S : Set V)
    · obtain ⟨a, b, hab, hua, hub⟩ := hdeg v
      exact ⟨a, by simpa using fun ha => (G.ne_of_adj hua) (hpair a ha v hv).symm⟩
    · exact ⟨v, by simpa using hv⟩
  obtain ⟨w, hw⟩ := hWne
  exact gt_total_forcing_poly_eq_stuck_notMem hSW hstuck w hw (hS w)

private lemma gt_total_forcing_poly_eq_no_isolated (t : ℕ) (ht : 24 ≤ t) (S : Finset (GtVertex t))
    (hS : is_zero_forcing_set (gt_graph t) (S : Set (GtVertex t))) :
    ∀ v : (S : Set (GtVertex t)), ∃ w : (S : Set (GtVertex t)),
      (gt_graph t).Adj (v : GtVertex t) (w : GtVertex t) := by
  haveI : Nonempty (GtVertex t) := ⟨GtVertex.A 0⟩
  have hcard : 2 ≤ S.card :=
    gt_total_forcing_poly_eq_card_two_le (gt_total_forcing_poly_eq_two_neighbors t) hS
  obtain ⟨i, hiS⟩ := gt_total_forcing_poly_eq_exists_R t ht hS
  intro v
  by_cases hv : (v : GtVertex t) = GtVertex.R i
  · have hother : ∃ w ∈ S, w ≠ GtVertex.R i := by
      by_contra hh
      push Not at hh
      have hle : S.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [hh a ha, hh b hb]
      omega
    obtain ⟨w, hwS, hwne⟩ := hother
    exact ⟨⟨w, hwS⟩, by
      rw [hv]
      exact (gt_total_forcing_poly_eq_adj_to_R i hwne).symm⟩
  · exact ⟨⟨GtVertex.R i, hiS⟩, gt_total_forcing_poly_eq_adj_to_R i hv⟩

/-- Total forcing polynomial of G_t equals its zero forcing polynomial. -/
theorem gt_total_forcing_poly_eq (t : ℕ) (ht : 24 ≤ t) :
    total_forcing_poly (gt_graph t) = zero_forcing_poly (gt_graph t) := by
  dsimp [total_forcing_poly, zero_forcing_poly]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  by_cases h : is_zero_forcing_set (gt_graph t) (↑S : Set (GtVertex t))
  · have ht' : is_total_forcing_set (gt_graph t) (↑S : Set (GtVertex t)) :=
      ⟨h, gt_total_forcing_poly_eq_no_isolated t ht S h⟩
    simp [h, ht']
  · have ht' : ¬ is_total_forcing_set (gt_graph t) (↑S : Set (GtVertex t)) :=
      fun hh => h hh.1
    simp [h, ht']
