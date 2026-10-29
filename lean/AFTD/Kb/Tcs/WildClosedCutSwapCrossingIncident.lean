import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_swap_crossing_incident

Topic: graphs   Node: 9625fba4fb3b

Provenance: helper lemma. Helper for the structural exchange route in the OP-306 campaign on arXiv:2610.22142. This records a cut obstruction or a sufficient test for exchanges, not a new wild-number bound.

For any proper edge coloring of a complete graph, if swapping vertices a and b in a vertex cut U makes U closed for color i, every old color-i edge crossing U has an endpoint among a and b.
-/

open scoped Classical
set_option maxHeartbeats 1000000

theorem wild_closed_cut_swap_crossing_incident {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (i : Fin k) (U : Finset (Fin n)) (a b : Fin n)
    (hclosed : w279_closed c i (U.image (Equiv.swap a b)))
    (u v : Fin n) (huv : u ≠ v) (hu : u ∈ U) (hv : v ∉ U)
    (hc : c ⟨s(u,v),wild_kn_mem huv⟩ = i) :
    u = a ∨ u = b ∨ v = a ∨ v = b := by
  by_contra! h
  have hsu : Equiv.swap a b u = u := Equiv.swap_apply_of_ne_of_ne h.1 h.2.1
  have hsv : Equiv.swap a b v = v := Equiv.swap_apply_of_ne_of_ne h.2.2.1 h.2.2.2
  have hu' : u ∈ U.image (Equiv.swap a b) := Finset.mem_image.2 ⟨u,hu,hsu⟩
  have hv' := hclosed u hu' v huv hc
  obtain ⟨w,hw,he⟩ := Finset.mem_image.1 hv'
  have hwv : w = v := (Equiv.swap a b).injective (he.trans hsv.symm)
  exact hv (hwv ▸ hw)
