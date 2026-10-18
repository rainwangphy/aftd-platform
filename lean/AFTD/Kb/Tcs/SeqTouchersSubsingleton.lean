import AFTD.Prelude
import AFTD.Kb.Tcs.HandshakeCleanUpdateContamSubsetToucher
import AFTD.Kb.Tcs.SeqTouchersSubsetContam
import AFTD.Kb.Tcs.SeqTouchers
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.HandshakeUpdateContam
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HandshakeTouchers

/-!
# seq_touchers_subsingleton

Topic: combinatorics   Node: cec58573c6db

Provenance: helper lemma. step towards glove_number_k4

In a clean handshake sequence, each glove side is directly touched by at most one vertex: the set of touching vertices of a side is a subsingleton.
-/

theorem seq_touchers_subsingleton_handshake_clean_contam_subset_toucher {V : Type*} {Γ : Type*} [DecidableEq Γ]
    {h : Handshake V Γ} {t : Γ × Bool → Set V} (hc : handshake_is_clean h t)
    {s : Γ × Bool} {w : V} (hw : w ∈ handshake_touchers h s) :
    t s ⊆ {w} := by
  cases h with
  | single x a y =>
    simp only [handshake_is_clean] at hc
    rcases hc with ⟨hxa, hya⟩
    simp only [handshake_touchers] at hw
    by_cases hsa : s = a
    · subst hsa
      simp only [if_true] at hw
      have : w = x := hw
      subst this
      exact hxa
    · simp only [if_neg hsa] at hw
      by_cases hso : s = opp_glove_side a
      · subst hso
        simp only [if_true] at hw
        have : w = y := hw
        subst this
        exact hya
      · simp only [if_neg hso] at hw
        cases hw
  | double x a b y =>
    simp only [handshake_is_clean] at hc
    rcases hc with ⟨hne, hxa, hyb⟩
    simp only [handshake_touchers] at hw
    by_cases hsa : s = a
    · subst hsa
      simp only [if_true] at hw
      have : w = x := hw
      subst this
      exact hxa
    · simp only [if_neg hsa] at hw
      by_cases hsb : s = b
      · subst hsb
        simp only [if_true] at hw
        have : w = y := hw
        subst this
        exact hyb
      · simp only [if_neg hsb] at hw
        cases hw

theorem seq_touchers_subsingleton_eq_of_mem_contam {V : Type*} {Γ : Type*} [DecidableEq Γ]
    {seq : List (Handshake V Γ)} {t : Γ × Bool → Set V} (h : CleanHandshakeSeq seq t)
    {s : Γ × Bool} {v : V} (hv : v ∈ t s) {w : V} (hw : w ∈ seq_touchers seq s) :
    w = v := by
  induction h with
  | nil =>
    cases hw
  | cons head tl t_init hc htl ih =>
    cases hw with
    | inl htouch =>
      have ht_sub : t_init s ⊆ {w} := seq_touchers_subsingleton_handshake_clean_contam_subset_toucher hc htouch
      have : v ∈ ({w} : Set V) := ht_sub hv
      exact this.symm
    | inr hrest =>
      have hv' : v ∈ handshake_update_contam head t_init s :=
        seq_touchers_subset_contam_contam_mono_step head t_init s hv
      exact ih hv' hrest

/-- A single glove side is touched by at most one vertex over a clean sequence. -/
theorem seq_touchers_subsingleton {V : Type*} {Γ : Type*} [DecidableEq Γ]
    (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V) (h : CleanHandshakeSeq seq t)
    (s : Γ × Bool) : (seq_touchers seq s).Subsingleton := by
  induction h with
  | nil =>
    intro a ha
    cases ha
  | cons head tl t_init hc htl ih =>
    intro a ha b hb
    cases ha with
    | inl ha_head =>
      cases hb with
      | inl hb_head =>
        have h_up : handshake_update_contam head t_init s ⊆ {a} :=
          handshake_clean_update_contam_subset_toucher hc ha_head
        have hb_in_up : b ∈ handshake_update_contam head t_init s :=
          seq_touchers_subset_contam_handshake_touchers_subset_contam_step head t_init s hb_head
        have : b ∈ ({a} : Set V) := h_up hb_in_up
        exact this.symm
      | inr hb_tl =>
        have ha_in_up : a ∈ handshake_update_contam head t_init s :=
          seq_touchers_subset_contam_handshake_touchers_subset_contam_step head t_init s ha_head
        have hb_eq_a : b = a := seq_touchers_subsingleton_eq_of_mem_contam htl ha_in_up hb_tl
        exact hb_eq_a.symm
    | inr ha_tl =>
      cases hb with
      | inl hb_head =>
        have hb_in_up : b ∈ handshake_update_contam head t_init s :=
          seq_touchers_subset_contam_handshake_touchers_subset_contam_step head t_init s hb_head
        exact seq_touchers_subsingleton_eq_of_mem_contam htl hb_in_up ha_tl
      | inr hb_tl =>
        exact ih ha_tl hb_tl
