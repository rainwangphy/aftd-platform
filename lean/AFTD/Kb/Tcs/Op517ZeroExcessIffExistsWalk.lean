import AFTD.Prelude
import AFTD.Kb.Tcs.BruhatOrderThreeGraph
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_517_zero_excess_iff_exists_walk

Topic: np_completeness   Node: 573c3656e826

Provenance: formalization of a published result. Source: arXiv:2610.03808 Lemma 2.8

Two rank-3 signotopes on Fin m have braid-move excess 0 if and only if there exists a walk in the higher Bruhat order B(m, 2) between them whose length equals their Hamming distance.
-/

theorem op_517_zero_excess_iff_exists_walk_ot_inj (m : ℕ) :
    Function.Injective (fun t : OrderedTriple (Fin m) => (t.a, t.b, t.c)) := by
  intro ⟨xa, xb, xc, xab, xbc⟩ ⟨ya, yb, yc, yab, ybc⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

instance op_517_zero_excess_iff_exists_walk_ot_finite (m : ℕ) : Finite (OrderedTriple (Fin m)) :=
  Finite.of_injective (fun t : OrderedTriple (Fin m) => (t.a, t.b, t.c))
    (op_517_zero_excess_iff_exists_walk_ot_inj m)

theorem op_517_zero_excess_iff_exists_walk_support_le (m : ℕ)
    {u v : { w : OrderedTriple (Fin m) → ℤˣ // is_rank_three_signotope w }}
    (p : (bruhat_order_three_graph (Fin m)).Walk u v) :
    {t : OrderedTriple (Fin m) | u.val t ≠ v.val t}.ncard ≤ p.length := by
  induction' p with u' u' v' w' hadj p_rest ih
  · simp
  · rw [SimpleGraph.Walk.length_cons]
    obtain ⟨i₀, hi₀, huniq⟩ := hadj
    have heq : ∀ t, t ≠ i₀ → u'.val t = v'.val t := by
      intro t ht
      by_contra hne
      exact ht (huniq t hne)
    have hsub : {t | u'.val t ≠ w'.val t} ⊆ insert i₀ {t | v'.val t ≠ w'.val t} := by
      intro t ht
      by_cases hti : t = i₀
      · simp [hti]
      · right
        change v'.val t ≠ w'.val t
        have : u'.val t = v'.val t := heq t hti
        rw [← this]
        exact ht
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hinsert := Set.ncard_insert_le i₀ {t | v'.val t ≠ w'.val t}
    omega

/-- Zero excess is equivalent to the existence of a walk of length equal to the Hamming distance. -/
theorem op_517_zero_excess_iff_exists_walk (m : ℕ) (u v : OrderedTriple (Fin m) → ℤˣ)
    (hu : is_rank_three_signotope u) (hv : is_rank_three_signotope v) :
    (bruhat_order_three_graph (Fin m)).dist ⟨u, hu⟩ ⟨v, hv⟩ = {t : OrderedTriple (Fin m) | u t ≠ v t}.ncard ↔
      ∃ p : (bruhat_order_three_graph (Fin m)).Walk ⟨u, hu⟩ ⟨v, hv⟩,
        p.length = {t : OrderedTriple (Fin m) | u t ≠ v t}.ncard := by
  set G := bruhat_order_three_graph (Fin m)
  set D := {t : OrderedTriple (Fin m) | u t ≠ v t}.ncard
  constructor
  · intro h
    by_cases hD : D = 0
    · have h_empty : {t : OrderedTriple (Fin m) | u t ≠ v t} = ∅ := by
        rwa [Set.ncard_eq_zero] at hD
      have huv : u = v := by
        funext t
        by_contra hc
        have ht : t ∈ {t : OrderedTriple (Fin m) | u t ≠ v t} := hc
        rw [h_empty] at ht
        exact ht
      subst huv
      refine ⟨SimpleGraph.Walk.nil, hD.symm⟩
    · have hdist_ne : G.dist ⟨u, hu⟩ ⟨v, hv⟩ ≠ 0 := by rw [h]; exact hD
      have hr : G.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := SimpleGraph.Reachable.of_dist_ne_zero hdist_ne
      obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist hr
      use p
      rw [hp, h]
  · rintro ⟨p, hp⟩
    have hle : G.dist ⟨u, hu⟩ ⟨v, hv⟩ ≤ D := by
      rw [← hp]
      exact SimpleGraph.dist_le p
    have hr : G.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := ⟨p⟩
    obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist hr
    have hge : D ≤ G.dist ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [← hq]
      exact op_517_zero_excess_iff_exists_walk_support_le m q
    exact le_antisymm hle hge
