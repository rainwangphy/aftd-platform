import AFTD.Prelude

/-!
# fin_forward_pairs_card

Topic: combinatorics   Node: 1256dc1cac27

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

For d at most g, the number of ordered pairs of elements of Fin g whose first value is the second value plus d is g-d.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem fin_forward_pairs_card (g d : ℕ) (hd : d ≤ g) :
    (((univ : Finset (Fin g)).product univ).filter
      (fun p : Fin g × Fin g => p.2.val+d = p.1.val)).card = g-d := by
  classical
  let S := ((univ : Finset (Fin g)).product univ).filter
    (fun p : Fin g × Fin g => p.2.val+d = p.1.val)
  have he : (univ : Finset (Fin (g-d))).card = S.card := by
    apply card_bij (fun a ha => (⟨a.val+d, by omega⟩, ⟨a.val, by omega⟩))
    · intro a ha
      simp [S]
    · intro a ha b hb heq
      apply Fin.ext
      exact congrArg (fun p : Fin g × Fin g => p.2.val) heq
    · intro p hp
      have hp' : p.2.val+d = p.1.val := (mem_filter.mp hp).2
      have hpg : p.1.val < g := p.1.isLt
      have hpi : p.2.val < g-d := by omega
      refine ⟨⟨p.2.val, hpi⟩, mem_univ _, ?_⟩
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  simpa only [card_univ, Fintype.card_fin, S] using he.symm
