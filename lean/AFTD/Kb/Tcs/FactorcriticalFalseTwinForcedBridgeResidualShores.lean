import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalFalseTwinsForcedResidualEdgeIsBridge
import AFTD.Kb.Tcs.PerfectMatchingFalseTwinsSwitchPartner
import AFTD.Kb.Tcs.ForcedResidualMatchingEdgeExcludesFalseTwin
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching
import AFTD.Kb.Tcs.PerfectMatchingBridgeEvenShoresOnFinset
import AFTD.Kb.Tcs.ComplementDegreeResidualExtraNeighbor
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_false_twin_forced_bridge_residual_shores

Topic: graphs   Node: 8701f853419a

Provenance: helper lemma. OP-1957 bridge-to-shores conversion with all extra components grouped on the x side.

Every forced residual edge at a false twin in the stated factor-critical and degree setting gives two even nonendpoint bridge shores, without any codegree restriction.
-/

theorem factorcritical_false_twin_forced_bridge_residual_shores {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (hcrit : is_k_factor_critical G (2*k)) (hn : n = 2*k+d+3) (x y z : Fin n) (hxy : x ≠ y) (htwin : G.neighborSet x = G.neighborSet y) (hxz : G.Adj x z) (hmax : ∀ a, ((Gᶜ).neighborFinset a).card ≤ d) (R : Finset (Fin n)) (hR : R.card = d+3) (hx : x ∈ R) (hz : z ∈ R) (hmatch : ∃ P : (G.induce {a | a ∈ R}).Subgraph, P.IsPerfectMatching) (hforced : ¬ ∃ P : ((G.induce {a | a ∈ R}).deleteEdges {s(⟨x,hx⟩,⟨z,hz⟩)}).Subgraph, P.IsPerfectMatching) : y ∉ R ∧ ∃ Q W : Finset (Fin n), Disjoint Q W ∧ Q ∪ W ∪ {x,z} = R ∧ x ∉ Q ∧ z ∉ Q ∧ x ∉ W ∧ z ∉ W ∧ y ∉ Q ∧ y ∉ W ∧ 2 ≤ Q.card ∧ 2 ≤ W.card ∧ Even Q.card ∧ Even W.card ∧ Q.card + W.card = d+1 ∧ (∀ q ∈ Q, (Gᶜ).Adj z q) ∧ (∀ w ∈ W, (Gᶜ).Adj x w ∧ (Gᶜ).Adj y w) ∧ (∀ q ∈ Q, ∀ w ∈ W, (Gᶜ).Adj q w) := by
  classical
  have hy : y ∉ R := forced_residual_matching_edge_excludes_false_twin G R x y z hxy htwin hx hz hmatch hforced
  refine ⟨hy, ?_⟩
  obtain ⟨P,hP⟩ := hmatch
  have hxzP := perfect_matching_forced_edge_in_every_matching _ ⟨x,hx⟩ ⟨z,hz⟩ hforced P hP
  have hR' : R.card + 2*k = n := by omega
  have hbridge := factorcritical_false_twins_forced_residual_edge_is_bridge k n G hcrit R hR' x y z hxy htwin hx hz hy hxz hforced
  obtain ⟨Q,W,hdis,hpart,hxQ,hzQ,hxW,hzW,hqe,hwe,hzq,hxw,hcross⟩ :=
    perfect_matching_bridge_even_shores_on_finset G R x z hx hz P hP hxzP hbridge
  have hQR : Q ⊆ R := by
    intro a ha
    rw [← hpart]
    exact Finset.mem_union_left _ (Finset.mem_union_left W ha)
  have hWR : W ⊆ R := by
    intro a ha
    rw [← hpart]
    exact Finset.mem_union_left _ (Finset.mem_union_right Q ha)
  have hyQ : y ∉ Q := fun h => hy (hQR h)
  have hyW : y ∉ W := fun h => hy (hWR h)
  obtain ⟨a,haR,hax,haz,haxG⟩ := complement_degree_residual_extra_neighbor G R d hR x z hx hz hxz (hmax x)
  have haQ : a ∈ Q := by
    have ha : a ∈ Q ∪ W ∪ {x,z} := by rw [hpart]; exact haR
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (ha | ha) | ha | ha
    · exact ha
    · exact (hxw a ha haxG).elim
    · exact (hax ha).elim
    · exact (haz ha).elim
  obtain ⟨b,hbR,hbz,hbx,hbzG⟩ := complement_degree_residual_extra_neighbor G R d hR z x hz hx hxz.symm (hmax z)
  have hbW : b ∈ W := by
    have hb : b ∈ Q ∪ W ∪ {x,z} := by rw [hpart]; exact hbR
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with (hb | hb) | hb | hb
    · exact (hzq b hb hbzG).elim
    · exact hb
    · exact (hbx hb).elim
    · exact (hbz hb).elim
  have hqmin : 2 ≤ Q.card := by
    have hp : 0 < Q.card := Finset.card_pos.mpr ⟨a,haQ⟩
    obtain ⟨m,hm⟩ := hqe
    omega
  have hwmin : 2 ≤ W.card := by
    have hp : 0 < W.card := Finset.card_pos.mpr ⟨b,hbW⟩
    obtain ⟨m,hm⟩ := hwe
    omega
  have hpair : Disjoint (Q ∪ W) ({x,z} : Finset (Fin n)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hp
    simp only [Finset.mem_union] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hc.elim hxQ hxW
    · exact hc.elim hzQ hzW
  have hsum : Q.card + W.card = d+1 := by
    have hc := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hpair, Finset.card_union_of_disjoint hdis,
      Finset.card_pair hxz.ne, hR] at hc
    omega
  refine ⟨Q,W,hdis,hpart,hxQ,hzQ,hxW,hzW,hyQ,hyW,hqmin,hwmin,hqe,hwe,hsum,?_,?_,?_⟩
  · intro q hq
    exact ⟨fun h => hzQ (h ▸ hq), hzq q hq⟩
  · intro w hw
    have hwx : x ≠ w := fun h => hxW (h ▸ hw)
    have hwy : y ≠ w := fun h => hyW (h ▸ hw)
    have hny : ¬ G.Adj y w := by
      intro h
      apply hxw w hw
      exact (Set.ext_iff.mp htwin w).mpr h
    exact ⟨⟨hwx,hxw w hw⟩, ⟨hwy,hny⟩⟩
  · intro q hq w hw
    have hne : q ≠ w := fun h => (Finset.disjoint_left.mp hdis) hq (h ▸ hw)
    exact ⟨hne,hcross q hq w hw⟩
