import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_eq_half_add_of_leaf_neighbor

Topic: graphs   Node: 805c9bc632ea

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

Leaf recursion: if ℓ is a leaf neighbour of v (G.Adj v ℓ and deg ℓ = 1), then avd_v(G) = 1/2 + avd_v(G - ℓ), where G - ℓ is the subgraph induced on V \ {ℓ} (which still contains v). Equivalently, the paper's identity (6) with l = 1.
-/

/-- Deleting a leaf neighbour of v costs exactly 1/2 in the local average order: avd_v(G) = 1/2 + avd_v(G - ℓ). -/
theorem simple_graph_local_avg_dominating_order_eq_half_add_of_leaf_neighbor {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {v ℓ : V}
    (hadj : G.Adj v ℓ) (hdeg : G.degree ℓ = 1) :
    simple_graph_local_avg_dominating_order G v =
      1 / 2 + simple_graph_local_avg_dominating_order
        (G.induce ((Finset.univ.erase ℓ : Finset V) : Set V))
        ⟨v, by simpa using G.ne_of_adj hadj⟩ := by
  classical
  set A : Finset V := Finset.univ.erase ℓ with hA
  have hmemv : v ∈ A := by simp [hA, G.ne_of_adj hadj]
  set H : SimpleGraph ↥((A : Finset V) : Set V) := G.induce ((A : Finset V) : Set V) with hH
  set D : Finset (Finset V) := simple_graph_dominating_sets_containing G v with hD
  set D' : Finset (Finset ↥((A : Finset V) : Set V)) :=
    simple_graph_dominating_sets_containing H ⟨v, hmemv⟩ with hD'
  set D₀ : Finset (Finset V) := D.filter (fun S : Finset V => ℓ ∉ S) with hD₀
  set D₁ : Finset (Finset V) := D.filter (fun S : Finset V => ℓ ∈ S) with hD₁
  show simple_graph_local_avg_dominating_order G v =
    1 / 2 + simple_graph_local_avg_dominating_order H ⟨v, hmemv⟩
  have memD : ∀ S : Finset V, S ∈ D ↔ v ∈ S ∧ ∀ w : V, w ∈ S ∨ ∃ u ∈ S, G.Adj u w := by
    intro S; rw [hD]; simp [simple_graph_dominating_sets_containing]
  have memD' : ∀ T : Finset ↥((A : Finset V) : Set V),
      T ∈ D' ↔ ⟨v, hmemv⟩ ∈ T ∧
        ∀ w : ↥((A : Finset V) : Set V), w ∈ T ∨ ∃ u ∈ T, H.Adj u w := by
    intro T; rw [hD']; simp [simple_graph_dominating_sets_containing]
  have memD₀ : ∀ S : Finset V, S ∈ D₀ ↔ S ∈ D ∧ ℓ ∉ S := by
    intro S; rw [hD₀]; simp
  have memD₁ : ∀ S : Finset V, S ∈ D₁ ↔ S ∈ D ∧ ℓ ∈ S := by
    intro S; rw [hD₁]; simp
  have huniq : ∀ w : V, G.Adj ℓ w → w = v := by
    intro w hw
    obtain ⟨x, hx, hxu⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := G) (v := ℓ)).mp hdeg
    have hvx : v = x := hxu v hadj.symm
    have hwx : w = x := hxu w hw
    rw [hwx, ← hvx]
  have hadjH : ∀ u w : ↥((A : Finset V) : Set V), H.Adj u w ↔ G.Adj u.1 w.1 := by
    intro u w; rw [hH]; exact SimpleGraph.induce_adj
  have erase_mem : ∀ S ∈ D, S.erase ℓ ∈ D := by
    intro S hS
    obtain ⟨hvS, hdom⟩ := (memD S).mp hS
    rw [memD]
    refine ⟨Finset.mem_erase.mpr ⟨G.ne_of_adj hadj, hvS⟩, ?_⟩
    intro w
    by_cases hw : w = ℓ
    · subst hw
      exact Or.inr ⟨v, Finset.mem_erase.mpr ⟨G.ne_of_adj hadj, hvS⟩, hadj⟩
    · by_cases hwS : w ∈ S
      · exact Or.inl (Finset.mem_erase.mpr ⟨hw, hwS⟩)
      · rcases hdom w with h | ⟨u, huS, huadj⟩
        · exact absurd h hwS
        · refine Or.inr ⟨u, Finset.mem_erase.mpr ⟨?_, huS⟩, huadj⟩
          rintro rfl
          exact hwS (by rw [huniq w huadj]; exact hvS)
  have insert_mem : ∀ S ∈ D, insert ℓ S ∈ D := by
    intro S hS
    obtain ⟨hvS, hdom⟩ := (memD S).mp hS
    rw [memD]
    refine ⟨Finset.mem_insert_of_mem hvS, ?_⟩
    intro w
    rcases hdom w with h | ⟨u, huS, huadj⟩
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr ⟨u, Finset.mem_insert_of_mem huS, huadj⟩
  have hi : ∀ S ∈ D₀, insert ℓ S ∈ D₁ := by
    intro S hS
    obtain ⟨hSD, hℓS⟩ := (memD₀ S).mp hS
    rw [memD₁]
    exact ⟨insert_mem S hSD, Finset.mem_insert_self ℓ S⟩
  have hj : ∀ S ∈ D₁, S.erase ℓ ∈ D₀ := by
    intro S hS
    obtain ⟨hSD, hℓS⟩ := (memD₁ S).mp hS
    rw [memD₀]
    exact ⟨erase_mem S hSD, by simp⟩
  have hleft : ∀ S ∈ D₀, (insert ℓ S).erase ℓ = S := by
    intro S hS; exact Finset.erase_insert ((memD₀ S).mp hS).2
  have hright : ∀ S ∈ D₁, insert ℓ (S.erase ℓ) = S := by
    intro S hS; exact Finset.insert_erase ((memD₁ S).mp hS).2
  have hcard_eq : D₀.card = D₁.card :=
    Finset.card_nbij' (fun S : Finset V => insert ℓ S) (fun S : Finset V => S.erase ℓ) hi hj hleft hright
  have hunion : D₁ ∪ D₀ = D := by
    rw [hD₁, hD₀, hD]
    exact Finset.filter_union_filter_not_eq (fun S : Finset V => ℓ ∈ S) D
  have hdisj : Disjoint D₁ D₀ := by
    rw [hD₁, hD₀]
    exact Finset.disjoint_filter_filter_not D D (fun S : Finset V => ℓ ∈ S)
  have hsum_split : (∑ S ∈ D, (S.card : ℚ)) = (∑ S ∈ D₀, (S.card : ℚ)) + (∑ S ∈ D₁, (S.card : ℚ)) := by
    rw [← hunion, Finset.sum_union hdisj, add_comm]
  have hcard_split : D.card = D₀.card + D₁.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, add_comm]
  have hcard : D.card = 2 * D₀.card := by omega
  have hshift : (∑ S ∈ D₁, (S.card : ℚ)) = (∑ S ∈ D₀, (S.card : ℚ)) + (D₀.card : ℚ) := by
    have h := Finset.sum_nbij' (s := D₀) (t := D₁)
      (f := fun S : Finset V => (S.card : ℚ) + 1) (g := fun S : Finset V => (S.card : ℚ))
      (fun S : Finset V => insert ℓ S) (fun S : Finset V => S.erase ℓ) hi hj hleft hright
      (fun S hS => by rw [Finset.card_insert_of_notMem ((memD₀ S).mp hS).2]; push_cast; ring)
    rw [← h, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfil : ∀ S ∈ D₀, S.filter (fun x : V => x ∈ ((A : Finset V) : Set V)) = S := by
    intro S hS
    rw [Finset.filter_eq_self]
    intro x hx
    have hℓS : ℓ ∉ S := ((memD₀ S).mp hS).2
    simp only [hA, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_coe]
    intro hxℓ
    exact hℓS (hxℓ ▸ hx)
  have hcomp1 : ∀ S ∈ D₀, Finset.map (Function.Embedding.subtype (fun x : V => x ∈ ((A : Finset V) : Set V)))
      (Finset.subtype (fun x : V => x ∈ ((A : Finset V) : Set V)) S) = S := by
    intro S hS
    rw [Finset.subtype_map]
    exact hfil S hS
  have hcomp2 : ∀ T ∈ D', Finset.subtype (fun x : V => x ∈ ((A : Finset V) : Set V))
      (Finset.map (Function.Embedding.subtype (fun x : V => x ∈ ((A : Finset V) : Set V))) T) = T := by
    intro T _
    ext a
    simp [Finset.mem_subtype]
  have hsub : ∀ S ∈ D₀, Finset.subtype (fun x : V => x ∈ ((A : Finset V) : Set V)) S ∈ D' := by
    intro S hS
    obtain ⟨hSD, hℓS⟩ := (memD₀ S).mp hS
    obtain ⟨hvS, hdom⟩ := (memD S).mp hSD
    rw [memD']
    refine ⟨Finset.mem_subtype.mpr hvS, ?_⟩
    intro w
    by_cases hwS : w.1 ∈ S
    · exact Or.inl (Finset.mem_subtype.mpr hwS)
    · rcases hdom w.1 with h | ⟨u, huS, huadj⟩
      · exact absurd h hwS
      · have huℓ : u ≠ ℓ := by
          rintro rfl
          exact hwS (by rw [huniq w.1 huadj]; exact hvS)
        refine Or.inr ⟨⟨u, ?_⟩, Finset.mem_subtype.mpr huS, ?_⟩
        · simp only [hA, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_coe]
          exact huℓ
        · rw [hadjH]; exact huadj
  have hmap : ∀ T ∈ D', Finset.map (Function.Embedding.subtype (fun x : V => x ∈ ((A : Finset V) : Set V))) T ∈ D₀ := by
    intro T hT
    obtain ⟨hv'T, hdom⟩ := (memD' T).mp hT
    rw [memD₀, memD]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_map.mpr ⟨⟨v, hmemv⟩, hv'T, rfl⟩
    · intro w
      by_cases hw : w = ℓ
      · subst hw
        exact Or.inr ⟨v, Finset.mem_map.mpr ⟨⟨v, hmemv⟩, hv'T, rfl⟩, hadj⟩
      · have hwA : w ∈ A := by simp [hA, hw]
        rcases hdom ⟨w, hwA⟩ with h | ⟨u, huT, huadj⟩
        · exact Or.inl (Finset.mem_map.mpr ⟨⟨w, hwA⟩, h, rfl⟩)
        · exact Or.inr ⟨u.1, Finset.mem_map.mpr ⟨u, huT, rfl⟩, (hadjH u ⟨w, hwA⟩).mp huadj⟩
    · intro hℓ
      obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hℓ
      have haA : a.1 ∈ A := a.2
      have h1 : a.1 = ℓ := by simpa using ha
      rw [h1] at haA
      simp [hA] at haA
  have hsum_trans : (∑ S ∈ D₀, (S.card : ℚ)) = (∑ T ∈ D', (T.card : ℚ)) := by
    refine Finset.sum_nbij' (s := D₀) (t := D')
      (f := fun S : Finset V => (S.card : ℚ)) (g := fun T : Finset ↥((A : Finset V) : Set V) => (T.card : ℚ))
      (fun S : Finset V => Finset.subtype (fun x : V => x ∈ ((A : Finset V) : Set V)) S)
      (fun T => Finset.map (Function.Embedding.subtype (fun x : V => x ∈ ((A : Finset V) : Set V))) T)
      hsub hmap hcomp1 hcomp2 ?_
    intro S hS
    rw [Finset.card_subtype (fun x : V => x ∈ ((A : Finset V) : Set V)) S, hfil S hS]
  have hcard_trans : D₀.card = D'.card :=
    Finset.card_nbij' (fun S : Finset V => Finset.subtype (fun x : V => x ∈ ((A : Finset V) : Set V)) S)
      (fun T => Finset.map (Function.Embedding.subtype (fun x : V => x ∈ ((A : Finset V) : Set V))) T)
      hsub hmap hcomp1 hcomp2
  have hD₀ne : D₀.Nonempty := by
    refine ⟨Finset.univ.erase ℓ, ?_⟩
    rw [memD₀]
    refine ⟨erase_mem Finset.univ ?_, by simp⟩
    rw [memD]
    exact ⟨Finset.mem_univ v, fun w => Or.inl (Finset.mem_univ w)⟩
  have hG : simple_graph_local_avg_dominating_order G v = (∑ S ∈ D, (S.card : ℚ)) / (D.card : ℚ) := by
    rw [simple_graph_local_avg_dominating_order, ← hD]
  have hH' : simple_graph_local_avg_dominating_order H ⟨v, hmemv⟩ =
      (∑ T ∈ D', (T.card : ℚ)) / (D'.card : ℚ) := by
    rw [simple_graph_local_avg_dominating_order, ← hD']
  rw [hG, hH']
  have hmain : (∑ S ∈ D, (S.card : ℚ)) = 2 * (∑ S ∈ D₀, (S.card : ℚ)) + (D₀.card : ℚ) := by
    rw [hsum_split, hshift]; ring
  have hcardq : (D.card : ℚ) = 2 * (D₀.card : ℚ) := by rw [hcard]; push_cast; ring
  have hcardq' : (D'.card : ℚ) = (D₀.card : ℚ) := by rw [← hcard_trans]
  have hn : (D₀.card : ℚ) ≠ 0 := by
    have h : 0 < D₀.card := Finset.card_pos.mpr hD₀ne
    exact_mod_cast h.ne'
  rw [hmain, hcardq, ← hsum_trans, hcardq']
  field_simp
  ring
