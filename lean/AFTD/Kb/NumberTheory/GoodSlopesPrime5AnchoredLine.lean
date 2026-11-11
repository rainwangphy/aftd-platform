import AFTD.Prelude

/-!
# good_slopes_prime5_anchored_line

Topic: elementary_number_theory   Node: e79177c2c347

Provenance: helper lemma. Finite prime-plane direction lemma for the 35-point fiber route to OP-1027; compare arXiv:2611.01465, Lemma 4.7.

A set of five points over the field with five elements that contains (0,0) and (1,4), and on which y+2x, y+3x and y+4x are injective, lies on the line y+x=0.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

private def form5 (a : ZMod 5) (p : ZMod 5 × ZMod 5) := p.2 + a * p.1

private theorem prime5_compatibility_table : ∀ p q : ZMod 5 × ZMod 5,
    p.2 + p.1 ≠ 0 →
    (∀ a : ZMod 5, a = 2 ∨ a = 3 ∨ a = 4 →
      (form5 a p = form5 a (0,0) → p = (0,0)) ∧
      (form5 a p = form5 a (1,4) → p = (1,4)) ∧
      (form5 a q = form5 a (0,0) → q = (0,0)) ∧
      (form5 a q = form5 a (1,4) → q = (1,4)) ∧
      (form5 a p = form5 a q → p = q)) →
    q = (0,0) ∨ q = (1,4) ∨ q = p := by decide

theorem good_slopes_prime5_anchored_line (S : Finset (ZMod 5 × ZMod 5))
    (hcard : S.card = 5) (h0 : (0,0) ∈ S) (h1 : (1,4) ∈ S)
    (h2 : Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + 2 * p.1) S) (h3 : Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + 3 * p.1) S)
    (h4 : Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + 4 * p.1) S) : ∀ p ∈ S, p.2 + p.1 = 0 := by
  classical
  change Set.InjOn (form5 2) S at h2
  change Set.InjOn (form5 3) S at h3
  change Set.InjOn (form5 4) S at h4
  intro p hp
  by_contra hpbad
  have hinj : ∀ a : ZMod 5, a = 2 ∨ a = 3 ∨ a = 4 → Set.InjOn (form5 a) S := by
    intro a ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hsub : S ⊆ {(0,0), (1,4), p} := by
    intro q hq
    have ht := prime5_compatibility_table p q hpbad (by
      intro a ha
      have hi := hinj a ha
      exact ⟨fun h => hi hp h0 h, fun h => hi hp h1 h,
        fun h => hi hq h0 h, fun h => hi hq h1 h, fun h => hi hp hq h⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hc := Finset.card_le_card hsub
  have hbound : ({(0,0), (1,4), p} : Finset (ZMod 5 × ZMod 5)).card ≤ 3 := Finset.card_le_three
  omega
