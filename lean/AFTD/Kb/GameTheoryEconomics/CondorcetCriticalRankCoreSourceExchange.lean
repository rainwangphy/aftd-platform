import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalRankCoreParetoAntichain

/-!
# condorcet_critical_rank_core_source_exchange

Topic: social_choice   Node: 0085d655d2ff

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

For positive k and n=k+q, a nonempty induced S_k subset of a rank relation whose vertices all have q active indices and satisfy the contained-signature Pareto antichain condition admits a source for each restricted activity set. For each vertex a and inactive index j there is a predecessor r of a, active at j, with signature contained in that of a plus j, also preceding every source of an index outside that union. Sources of nonempty restricted activity sets belong to those sets; all sources belong to B.
-/

open Finset
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000

theorem condorcet_critical_rank_core_source_exchange
    {m n k q : ℕ} (hk : 0 < k) (hn : n = k + q)
    (U : Fin n → Finset (Fin m)) (p : Fin n → Fin m → ℕ)
    (B : Finset (Fin m)) (hBne : B.Nonempty)
    (hcard : ∀ a ∈ B, (univ.filter fun v => a ∈ U v).card = q)
    (hroot : ∀ J : Finset (Fin m), J ⊆ B → J.card ≤ k →
      ∃ r, r ∈ B ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation U p r c)
    (hanti : ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
      (∀ v, a ∈ U v → b ∈ U v) →
      ∃ v, a ∈ U v ∧ p v b < p v a) :
    ∃ s : Fin n → Fin m,
      (∀ v, s v ∈ B) ∧
      (∀ v, (B ∩ U v).Nonempty → s v ∈ U v) ∧
      (∀ v, ∀ r ∈ B, r ∈ U v → ¬condorcet_cover_rank_relation U p r (s v)) ∧
      ∀ a ∈ B, ∀ j : Fin n, a ∉ U j →
        ∃ r, r ∈ B ∧ condorcet_cover_rank_relation U p r a ∧ r ∈ U j ∧
          (∀ v, r ∈ U v → a ∈ U v ∨ v = j) ∧
          (∀ v, v ≠ j → a ∉ U v → condorcet_cover_rank_relation U p r (s v)) := by
  classical
  obtain ⟨b,hb⟩ := hBne
  have hex : ∀ v : Fin n, ∃ s, s ∈ B ∧
      ((B ∩ U v).Nonempty → s ∈ U v) ∧
      ∀ r ∈ B, r ∈ U v → ¬condorcet_cover_rank_relation U p r s := by
    intro v
    by_cases hnon : (B ∩ U v).Nonempty
    · obtain ⟨s,hs,hmin⟩ := (B ∩ U v).exists_min_image (p v) hnon
      refine ⟨s,(mem_inter.mp hs).1,fun _ => (mem_inter.mp hs).2,?_⟩
      intro r hrB hrU hrs
      exact (not_lt_of_ge (hmin r (mem_inter.mpr ⟨hrB,hrU⟩)))
        (hrs.2 v hrU (mem_inter.mp hs).2)
    · exact ⟨b,hb,fun h => (hnon h).elim,fun r hrB hrU _ => hnon ⟨r,mem_inter.mpr ⟨hrB,hrU⟩⟩⟩
  choose s hsB hsU hs using hex
  refine ⟨s,hsB,hsU,hs,?_⟩
  intro a ha j haj
  let I := univ.filter fun v => a ∈ U v
  let W := univ \ insert j I
  have hI : I.card = q := hcard a ha
  have hjI : j ∉ I := by simpa only [I,mem_filter,mem_univ,true_and] using haj
  have hW : W.card = k - 1 := by
    dsimp only [W]
    rw [card_sdiff,inter_univ,card_univ,Fintype.card_fin,card_insert_of_notMem hjI,hI,hn]
    omega
  have hJsub : insert a (W.image s) ⊆ B := by
    apply insert_subset ha
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    exact hsB v
  have hJcard : (insert a (W.image s)).card ≤ k := by
    have hle := card_image_le (f := s) (s := W)
    have hle' := card_insert_le a (W.image s)
    omega
  obtain ⟨r,hrB,_,hr⟩ := hroot (insert a (W.image s)) hJsub hJcard
  have hra := hr a (mem_insert_self _ _)
  have htype : ∀ v, r ∈ U v → a ∈ U v ∨ v = j := by
    intro v hrv
    by_contra h
    push_neg at h
    have hvW : v ∈ W := by
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro hv
      rcases mem_insert.mp hv with hv | hv
      · exact h.2 hv
      · exact h.1 (mem_filter.mp hv).2
    exact hs v r hrB hrv
      (hr (s v) (mem_insert_of_mem (mem_image.mpr ⟨v,hvW,rfl⟩)))
  have hrj : r ∈ U j := by
    by_contra hnot
    have hsub : ∀ v, r ∈ U v → a ∈ U v := by
      intro v hv
      rcases htype v hv with h | rfl
      · exact h
      · exact (hnot hv).elim
    obtain ⟨v,hrv,hlt⟩ := hanti r hrB a ha hra.1 hsub
    exact (not_lt_of_ge (le_of_lt hlt)) (hra.2 v hrv (hsub v hrv))
  refine ⟨r,hrB,hra,hrj,htype,?_⟩
  intro v hvj hva
  apply hr (s v)
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨v,?_,rfl⟩
  apply mem_sdiff.mpr
  refine ⟨mem_univ _,?_⟩
  intro hv
  rcases mem_insert.mp hv with hv | hv
  · exact hvj hv
  · exact hva (mem_filter.mp hv).2
