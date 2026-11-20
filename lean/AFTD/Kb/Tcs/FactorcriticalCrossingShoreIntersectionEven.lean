import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven

/-!
# factorcritical_crossing_shore_intersection_even

Topic: graphs   Node: 8822a7628064

Provenance: helper lemma. OP-1957 four-shore crossing and repeated-shore analysis; scratch Lean axiom audit completed.

Factor-criticality makes crossing even bridge shores intersect evenly under the displayed cut conditions.
-/

theorem factorcritical_crossing_shore_intersection_even
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k d : ℕ) (hcrit : is_k_factor_critical G (2*k))
    (W₁ W₂ Q₁ Q₂ : Finset V) (z₁ z₂ : V)
    (hsize₁ : W₁.card+Q₁.card=d+1) (hsize₂ : W₂.card+Q₂.card=d+1)
    (hW₁even : Even W₁.card) (hW₂even : Even W₂.card) (hQ₁even : Even Q₁.card)
    (heq : (W₁ ∪ W₂).card + (Q₁ ∩ Q₂).card = d+1)
    (hcut : ((Finset.univ : Finset V) \ ((Q₁ ∩ Q₂) ∪ ((W₁ ∪ W₂) ∪ {z₁,z₂}))).card = 2*k)
    (hdisj : Disjoint (Q₁ ∩ Q₂) (W₁ ∪ W₂))
    (hz₁ : z₁ ∉ Q₁ ∩ Q₂) (hz₂ : z₂ ∉ Q₁ ∩ Q₂)
    (hcross₁ : ∀ w ∈ W₁, ∀ q ∈ Q₁, ¬ G.Adj w q)
    (hcross₂ : ∀ w ∈ W₂, ∀ q ∈ Q₂, ¬ G.Adj w q)
    (hend : ∀ q ∈ Q₁ ∩ Q₂, ¬ G.Adj q z₁ ∧ ¬ G.Adj q z₂) :
    Even (W₁ ∩ W₂).card := by
  classical
  have hd : Disjoint (Q₁ ∩ Q₂) ((W₁ ∪ W₂) ∪ {z₁,z₂}) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.disjoint_left.mp hdisj) ha hb
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact hz₁ ha
      · exact hz₂ ha
  have hc : ∀ q ∈ Q₁ ∩ Q₂, ∀ w ∈ (W₁ ∪ W₂) ∪ {z₁,z₂}, ¬ G.Adj q w := by
    intro q hq w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases Finset.mem_union.mp hw with hw | hw
      · intro hadj
        exact hcross₁ w hw q (Finset.mem_inter.mp hq).1 hadj.symm
      · intro hadj
        exact hcross₂ w hw q (Finset.mem_inter.mp hq).2 hadj.symm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (hend q hq).1
      · exact (hend q hq).2
  have hj := factor_critical_anticomplete_cut_side_even G (2*k) hcrit
    (Q₁ ∩ Q₂) ((W₁ ∪ W₂) ∪ {z₁,z₂}) hd hc hcut
  have hu := Finset.card_union_add_card_inter W₁ W₂
  obtain ⟨a,ha⟩ := hW₁even
  obtain ⟨b,hb⟩ := hW₂even
  obtain ⟨c,hc'⟩ := hQ₁even
  obtain ⟨e,he⟩ := hj
  refine ⟨b+e-c,?_⟩
  omega
