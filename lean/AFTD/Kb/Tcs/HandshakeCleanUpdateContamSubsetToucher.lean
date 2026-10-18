import AFTD.Prelude
import AFTD.Kb.Tcs.HandshakeTouchers
import AFTD.Kb.Tcs.HandshakeUpdateContam
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.HandshakeIsClean

/-!
# handshake_clean_update_contam_subset_toucher

Topic: combinatorics   Node: 95622a95cf41

Provenance: helper lemma. step towards glove_number_k4

If the handshake `h` is clean with respect to the contamination map `t` and the vertex `v` touches the side `s` during `h`, then after performing `h` the contamination of `s` is contained in `{v}`: a clean handshake lets a player touch a side only if that side carries nobody but them, and no merge can add anything to a side that is being touched. (The opposite sides of a double handshake are not touched, so nothing is claimed for them.)
-/

/-- A clean handshake leaves only its own toucher on the sides it touches. -/
theorem handshake_clean_update_contam_subset_toucher {V : Type*} {Γ : Type*} [DecidableEq Γ]
    {h : Handshake V Γ} {t : Γ × Bool → Set V} (hc : handshake_is_clean h t)
    {s : Γ × Bool} {v : V} (hv : v ∈ handshake_touchers h s) :
    handshake_update_contam h t s ⊆ {v} := by
  cases h with
  | single x a y =>
    simp only [handshake_is_clean] at hc
    rcases hc with ⟨hxa, hya⟩
    simp only [handshake_touchers, handshake_update_contam] at hv ⊢
    by_cases hsa : s = a
    · subst hsa
      simp only [if_true] at hv ⊢
      have hvx : v = x := hv
      subst hvx
      exact Set.union_subset hxa (Set.Subset.refl _)
    · simp only [if_neg hsa] at hv ⊢
      by_cases hso : s = opp_glove_side a
      · subst hso
        simp only [if_true] at hv ⊢
        have hvy : v = y := hv
        subst hvy
        exact Set.union_subset hya (Set.Subset.refl _)
      · simp only [if_neg hso] at hv
        cases hv
  | double x a b y =>
    simp only [handshake_is_clean] at hc
    rcases hc with ⟨hne, hxa, hyb⟩
    simp only [handshake_touchers, handshake_update_contam] at hv ⊢
    by_cases hsa : s = a
    · subst hsa
      simp only [if_true] at hv ⊢
      have hvx : v = x := hv
      subst hvx
      exact Set.union_subset hxa (Set.Subset.refl _)
    · simp only [if_neg hsa] at hv ⊢
      by_cases hsb : s = b
      · subst hsb
        simp only [if_true] at hv ⊢
        have hvy : v = y := hv
        subst hvy
        exact Set.union_subset hyb (Set.Subset.refl _)
      · simp only [if_neg hsb] at hv
        cases hv
