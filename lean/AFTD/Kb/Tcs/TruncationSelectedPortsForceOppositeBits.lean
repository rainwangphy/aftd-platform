import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# truncation_selected_ports_force_opposite_bits

Topic: graphs   Node: 6b611a960f47

Provenance: helper lemma. Local-state interface reduction for the OP-874 one-defect construction.

If each endpoint of an edge hides its missing low color on another port, disjoint exposed pairs force those endpoints to have different matching bits.
-/

open Set

theorem truncation_selected_ports_force_opposite_bits
    {V E : Type*} (ends : E → Sym2 V) (c h : V → E → Fin 6)
    (bit : V → Bool) (u v : V) (e f g : E)
    (hue : u ∈ ends e) (hve : v ∈ ends e)
    (huf : u ∈ ends f) (hvg : v ∈ ends g)
    (hfe : f ≠ e) (hge : g ≠ e)
    (hh : ∀ w a b, w ∈ ends a → w ∈ ends b → h w a = h w b → a = b)
    (hch : ∀ w a b, w ∈ ends a → w ∈ ends b → h w a ≠ c w b)
    (hd : Disjoint (truncation_exposed_pair ends c h u e)
                   (truncation_exposed_pair ends c h v e))
    (hfu : h u f = if bit u then 0 else 1)
    (hgv : h v g = if bit v then 0 else 1) :
    bit u ≠ bit v := by
  intro hb
  have heq : h u f = h v g := by rw [hfu, hgv, hb]
  have hm1 : h u f ∈ truncation_exposed_pair ends c h u e := by
    refine ⟨?_, ?_⟩
    · intro a ha
      exact (hch u f a huf ha).symm
    · intro he
      exact hfe (hh u f e huf hue he)
  have hm2 : h u f ∈ truncation_exposed_pair ends c h v e := by
    rw [heq]
    refine ⟨?_, ?_⟩
    · intro a ha
      exact (hch v g a hvg ha).symm
    · intro he
      exact hge (hh v g e hvg hve he)
  exact Set.disjoint_left.mp hd hm1 hm2
