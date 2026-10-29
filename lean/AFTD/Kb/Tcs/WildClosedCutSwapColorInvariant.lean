import AFTD.Prelude
import AFTD.Kb.Tcs.WildClosedCutSwapIff
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_swap_color_invariant

Topic: graphs   Node: 12fd452ba61c

Provenance: helper lemma. Helper for the structural exchange route in the OP-306 campaign on arXiv:2610.22142. This records a cut obstruction or a sufficient test for exchanges, not a new wild-number bound.

Swapping the endpoints of a color-i edge in a proper complete-graph edge coloring preserves whether each vertex cut is closed for color i.
-/

open scoped Classical
set_option maxHeartbeats 1000000

theorem wild_closed_cut_swap_color_invariant {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (i : Fin k) (U : Finset (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (hc : c ⟨s(a,b),wild_kn_mem hab⟩ = i) :
    w279_closed c i (U.image (Equiv.swap a b)) ↔ w279_closed c i U := by
  have fixed : ∀ (V : Finset (Fin n)), w279_closed c i V → V.image (Equiv.swap a b) = V := by
    intro V hV
    have hm : a ∈ V ↔ b ∈ V :=
      ⟨fun ha => hV a ha b hab hc,
       fun hb => hV b hb a (Ne.symm hab) ((w279_c_swap c (Ne.symm hab)).trans hc)⟩
    ext v
    rw [wild_swap_mem_image]
    by_cases hva : v = a
    · subst v; simpa only [Equiv.swap_apply_left] using hm.symm
    by_cases hvb : v = b
    · subst v; simpa only [Equiv.swap_apply_right] using hm
    rw [Equiv.swap_apply_of_ne_of_ne hva hvb]
  constructor
  · intro h
    have hf := fixed (U.image (Equiv.swap a b)) h
    have hh : (U.image (Equiv.swap a b)).image (Equiv.swap a b) = U := by
      ext v
      simp only [wild_swap_mem_image, Equiv.swap_apply_self]
    rw [hh] at hf
    simpa only [← hf] using h
  · intro h
    rw [fixed U h]
    exact h
