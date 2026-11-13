import AFTD.Prelude

/-!
# op1525_flip_neighborhood_injective

Topic: combinatorics   Node: 8ad457ceca10

Provenance: helper lemma. A bit-flip status lemma for the invariant-pair-orbit route to OP-1525.

On an index set with at least three points, a Boolean vector is determined by the set of its single-coordinate flips, even if only containment of that flip set in another vector’s flip set is assumed.
-/

theorem op1525_flip_neighborhood_injective {I : Type*} [DecidableEq I]
    (a b c : I) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f g : I → Bool)
    (h : ∀ i : I, ∃ j : I, ∀ k : I,
      xor (f k) (decide (k = i)) = xor (g k) (decide (k = j))) : f = g := by
  by_contra hne
  have hx : ∃ x, f x ≠ g x := by
    by_contra hx
    apply hne
    funext x
    by_contra hfxg
    exact hx ⟨x, hfxg⟩
  rcases hx with ⟨x, hxfg⟩
  have hpair : ∃ p q : I, p ≠ q ∧ p ≠ x ∧ q ≠ x := by
    by_cases hax : a = x
    · have hbx : b ≠ x := by
        intro hb
        exact hab (hax.trans hb.symm)
      have hcx : c ≠ x := by
        intro hc
        exact hac (hax.trans hc.symm)
      exact ⟨b, c, hbc, hbx, hcx⟩
    · by_cases hbx : b = x
      · have hcx : c ≠ x := by
          intro hc
          exact hbc (hbx.trans hc.symm)
        exact ⟨a, c, hac, hax, hcx⟩
      · exact ⟨a, b, hab, hax, hbx⟩
  rcases hpair with ⟨p, q, hpq, hpx, hqx⟩
  rcases h p with ⟨jp, hp⟩
  rcases h q with ⟨jq, hq⟩
  have hxp : x ≠ p := fun h' => hpx h'.symm
  have hxq : x ≠ q := fun h' => hqx h'.symm
  have hxjp : x = jp := by
    by_contra hxne
    have hdecp : decide (x = p) = false := by simp [hxp]
    have hdecj : decide (x = jp) = false := by simp [hxne]
    have := hp x
    simp only [hdecp, hdecj, Bool.xor_false] at this
    exact hxfg this
  have hxjq : x = jq := by
    by_contra hxne
    have hdecq : decide (x = q) = false := by simp [hxq]
    have hdecj : decide (x = jq) = false := by simp [hxne]
    have := hq x
    simp only [hdecq, hdecj, Bool.xor_false] at this
    exact hxfg this
  have hqp : q ≠ p := fun h' => hpq h'.symm
  have hqjp : q ≠ jp := by
    intro h'
    exact hqx (h'.trans hxjp.symm)
  have hpq_eq : f q = g q := by
    have := hp q
    have hdecqp : decide (q = p) = false := by simp [hqp]
    have hdecqjp : decide (q = jp) = false := by simp [hqjp]
    simp only [hdecqp, hdecqjp, Bool.xor_false] at this
    exact this
  have hq_neg : g q = ! f q := by
    have := hq q
    have hdecqjq : decide (q = jq) = false := by
      have hqjq : q ≠ jq := by
        intro h'
        exact hqx (hxjq.trans h'.symm).symm
      simp [hqjq]
    simp only [hdecqjq, Bool.xor_false, decide_true, Bool.xor_true] at this
    exact this.symm
  have hcontra : f q = ! f q := hpq_eq.trans hq_neg
  cases hfq : f q <;> simp [hfq] at hcontra
