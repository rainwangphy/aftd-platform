import AFTD.Prelude
import AFTD.Kb.Tcs.IsStrongOddColoring

/-!
# strong_odd_coloring_insert_vertex

Topic: graphs   Node: 29d4beecf9f7

Provenance: helper lemma. step towards sparse_strong_odd_five_list_coloring

Let g be a colouring of a finite simple graph G which is a strong odd colouring of G - v; if g v avoids the colours of all neighbours of v and also the colours of all their other neighbours, and every colour appears 0 or an odd number of times among the neighbours of v, then g is a strong odd colouring of G.
-/

/-- The local recolouring criterion for peeling one vertex: the colour inserted at `v` must avoid `N(v)`'s colours and the colours of the other neighbours of `N(v)`, and `N(v)` must already satisfy the odd condition. -/
theorem strong_odd_coloring_insert_vertex {V κ : Type} [Fintype V] [DecidableEq V]
    [DecidableEq κ] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (g : V → κ)
    (hout : is_strong_odd_coloring (G.induce {x | x ≠ v}) (fun x => g x.1))
    (hproper : ∀ u ∈ G.neighborFinset v, g v ≠ g u)
    (hfar : ∀ u ∈ G.neighborFinset v, ∀ w ∈ G.neighborFinset u, w ≠ v → g v ≠ g w)
    (hpar : ∀ c : κ, {u ∈ G.neighborFinset v | g u = c} = ∅ ∨
      Odd {u ∈ G.neighborFinset v | g u = c}.card) :
    is_strong_odd_coloring G g := by
  obtain ⟨hprop', hpar'⟩ := hout
  refine ⟨?_, ?_⟩
  · intro a b hab
    by_cases ha : a = v
    · subst ha
      exact hproper b ((SimpleGraph.mem_neighborFinset _ _ _).mpr hab)
    by_cases hb : b = v
    · subst hb
      exact (hproper a ((SimpleGraph.mem_neighborFinset _ _ _).mpr hab.symm)).symm
    · exact hprop' (u := ⟨a, ha⟩) (v := ⟨b, hb⟩) hab
  · intro x c
    by_cases hx : x = v
    · subst hx
      exact hpar c
    have hmap : (∀ u, G.Adj x u → g u = c → u ≠ v) →
        (G.neighborFinset x).filter (fun u => g u = c) =
        (((G.induce {y | y ≠ v}).neighborFinset ⟨x, hx⟩).filter
          (fun u => g u.1 = c)).map (Function.Embedding.subtype _) := by
      intro hnv
      ext w
      simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hw, hwc⟩
        have hw' : G.Adj x w := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
        exact ⟨⟨w, hnv w hw' hwc⟩, ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hw', hwc⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
        have hy' : (G.induce {y | y ≠ v}).Adj ⟨x, hx⟩ y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
        exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hy', hyc⟩
    have finish : (∀ u, G.Adj x u → g u = c → u ≠ v) →
        ((G.neighborFinset x).filter (fun u => g u = c) = ∅ ∨
          Odd ((G.neighborFinset x).filter (fun u => g u = c)).card) := by
      intro hnv
      rcases hpar' ⟨x, hx⟩ c with h | h
      · left
        rw [hmap hnv]
        exact Finset.map_eq_empty.mpr h
      · right
        rw [hmap hnv, Finset.card_map]
        exact h
    by_cases hxv : G.Adj x v
    · by_cases hc : g v = c
      · right
        have hone : (G.neighborFinset x).filter (fun u => g u = c) = {v} := by
          ext w
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
          constructor
          · rintro ⟨hw, hwc⟩
            by_contra hne
            exact hfar x ((SimpleGraph.mem_neighborFinset _ _ _).mpr hxv.symm) w
              ((SimpleGraph.mem_neighborFinset _ _ _).mpr hw) hne (hc.trans hwc.symm)
          · rintro rfl
            exact ⟨hxv, hc⟩
        rw [hone, Finset.card_singleton]
        exact odd_one
      · exact finish fun u _ huc huv => hc (huv ▸ huc)
    · exact finish fun u hu _ huv => hxv (huv ▸ hu)
