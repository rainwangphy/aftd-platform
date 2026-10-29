import AFTD.Prelude
import AFTD.Kb.Tcs.WildClosedCutSwapCrossingIncident
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_swap_iff

Topic: graphs   Node: fbb2a7d325bb

Provenance: helper lemma. Helper for the structural exchange route in the OP-306 campaign on arXiv:2610.22142. This records a cut obstruction or a sufficient test for exchanges, not a new wild-number bound.

Let a belong to U and b lie outside U. In any proper complete-graph edge coloring, the swapped cut is closed for i exactly when a has no i-neighbor in U, b has no i-neighbor outside U, ab is not colored i, and every old crossing i-edge has its U-end a or its other end b.
-/

open scoped Classical
set_option maxHeartbeats 1000000
lemma wild_swap_mem_image {n : ℕ} (U : Finset (Fin n)) (a b v : Fin n) :
    v ∈ U.image (Equiv.swap a b) ↔ Equiv.swap a b v ∈ U := by
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.1 hv
    simpa only [Equiv.swap_apply_self] using hu
  · intro hv
    exact Finset.mem_image.2 ⟨Equiv.swap a b v,hv,Equiv.swap_apply_self a b v⟩

theorem wild_closed_cut_swap_iff {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (i : Fin k) (U : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ U) (hb : b ∉ U) :
    w279_closed c i (U.image (Equiv.swap a b)) ↔
      (∀ w ∈ U, ∀ h : a ≠ w, c ⟨s(a,w),wild_kn_mem h⟩ ≠ i) ∧
      (∀ w ∉ U, ∀ h : b ≠ w, c ⟨s(b,w),wild_kn_mem h⟩ ≠ i) ∧
      (∀ h : a ≠ b, c ⟨s(a,b),wild_kn_mem h⟩ ≠ i) ∧
      (∀ u ∈ U, ∀ v ∉ U, ∀ h : u ≠ v,
        c ⟨s(u,v),wild_kn_mem h⟩ = i → u = a ∨ v = b) := by
  have hab : a ≠ b := fun he => hb (he ▸ ha)
  have ha' : a ∉ U.image (Equiv.swap a b) := by
    rw [wild_swap_mem_image, Equiv.swap_apply_left]; exact hb
  have hb' : b ∈ U.image (Equiv.swap a b) := by
    rw [wild_swap_mem_image, Equiv.swap_apply_right]; exact ha
  have hmem (v : Fin n) (hva : v ≠ a) (hvb : v ≠ b) :
      v ∈ U.image (Equiv.swap a b) ↔ v ∈ U := by
    rw [wild_swap_mem_image, Equiv.swap_apply_of_ne_of_ne hva hvb]
  constructor
  · intro hcl
    refine ⟨?_,?_,?_,?_⟩
    · intro w hw haw hc
      have hwb : w ≠ b := fun h => hb (h ▸ hw)
      have hw' := (hmem w (Ne.symm haw) hwb).2 hw
      exact ha' (hcl w hw' a (Ne.symm haw) ((w279_c_swap c (Ne.symm haw)).trans hc))
    · intro w hw hbw hc
      have hwa : w ≠ a := fun h => hw (h ▸ ha)
      exact hw ((hmem w hwa (Ne.symm hbw)).1 (hcl b hb' w hbw hc))
    · intro _ hc
      exact ha' (hcl b hb' a (Ne.symm hab) ((w279_c_swap c (Ne.symm hab)).trans hc))
    · intro u hu v hv huv hc
      have hi := wild_closed_cut_swap_crossing_incident c i U a b hcl u v huv hu hv hc
      have hub : u ≠ b := fun h => hb (h ▸ hu)
      have hva : v ≠ a := fun h => hv (h ▸ ha)
      tauto
  · rintro ⟨hA,hB,hAB,hCross⟩ u hu v huv hc
    by_cases hub : u = b
    · subst u
      have hvU : v ∈ U := by by_contra hvU; exact hB v hvU huv hc
      have hva : v ≠ a := by
        intro he
        subst v
        exact hAB hab ((w279_c_swap c hab).trans hc)
      have hvb : v ≠ b := Ne.symm huv
      exact (hmem v hva hvb).2 hvU
    · have hua : u ≠ a := fun he => ha' (he ▸ hu)
      have huU := (hmem u hua hub).1 hu
      by_cases hvb : v = b
      · exact hvb.symm ▸ hb'
      · have hva : v ≠ a := by
          intro he
          subst v
          exact hA u huU (Ne.symm huv) ((w279_c_swap c (Ne.symm huv)).trans hc)
        have hvU : v ∈ U := by
          by_contra hvU
          exact (hCross u huU v hvU huv hc).elim hua hvb
        exact (hmem v hva hvb).2 hvU
