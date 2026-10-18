import AFTD.Prelude
import AFTD.Kb.Tcs.HandshakeTouchers
import AFTD.Kb.Tcs.SeqTouchers
import AFTD.Kb.Tcs.SeqContam
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.HandshakeUpdateContam
import AFTD.Kb.Tcs.Handshake

/-!
# seq_touchers_subset_contam

Topic: combinatorics   Node: 1e80bb8480cb

Provenance: helper lemma. step towards glove_number_k4

Contamination is monotone in the following sense: after running the sequence `seq` from the contamination map `t`, the contamination of the glove side `s` contains every vertex that directly touched `s` during `seq` (and in particular contains `t s`). Formally: first, for one handshake `h` both `t s ⊆ handshake_update_contam h t s` and `handshake_touchers h s ⊆ handshake_update_contam h t s`; hence for a sequence `seq_touchers seq s ⊆ seq_contam seq t s`.
-/

lemma seq_touchers_subset_contam_contam_mono_step {V Γ : Type*} [DecidableEq Γ]
    (h : Handshake V Γ) (t : Γ × Bool → Set V) (s : Γ × Bool) :
    t s ⊆ handshake_update_contam h t s := by
  intro v hv
  cases h with
  | single x a y =>
    dsimp [handshake_update_contam]
    split_ifs with h1 h2
    · subst h1; exact Or.inl hv
    · subst h2; exact Or.inl hv
    · exact hv
  | double x a b y =>
    dsimp [handshake_update_contam]
    split_ifs with h1 h2 h3
    · subst h1; exact Or.inl hv
    · subst h2; exact Or.inl hv
    · cases h3 with
      | inl ha => subst ha; exact Or.inl hv
      | inr hb => subst hb; exact Or.inr hv
    · exact hv

lemma seq_touchers_subset_contam_contam_subset_seq_contam {V Γ : Type*} [DecidableEq Γ]
    (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V) (s : Γ × Bool) :
    t s ⊆ seq_contam seq t s := by
  induction seq generalizing t with
  | nil =>
    intro v hv
    exact hv
  | cons h tl ih =>
    intro v hv
    have h1 : v ∈ handshake_update_contam h t s := seq_touchers_subset_contam_contam_mono_step h t s hv
    exact ih (handshake_update_contam h t) h1

lemma seq_touchers_subset_contam_handshake_touchers_subset_contam_step {V Γ : Type*} [DecidableEq Γ]
    (h : Handshake V Γ) (t : Γ × Bool → Set V) (s : Γ × Bool) :
    handshake_touchers h s ⊆ handshake_update_contam h t s := by
  intro v hv
  cases h with
  | single x a y =>
    dsimp [handshake_touchers, handshake_update_contam] at *
    by_cases hsa : s = a
    · rw [if_pos hsa]
      rw [if_pos hsa] at hv
      exact Or.inr hv
    · rw [if_neg hsa]
      rw [if_neg hsa] at hv
      by_cases hso : s = opp_glove_side a
      · rw [if_pos hso]
        rw [if_pos hso] at hv
        exact Or.inr hv
      · rw [if_neg hso] at hv
        contradiction
  | double x a b y =>
    dsimp [handshake_touchers, handshake_update_contam] at *
    by_cases hsa : s = a
    · rw [if_pos hsa]
      rw [if_pos hsa] at hv
      exact Or.inr hv
    · rw [if_neg hsa]
      rw [if_neg hsa] at hv
      by_cases hsb : s = b
      · rw [if_pos hsb]
        rw [if_pos hsb] at hv
        exact Or.inr hv
      · rw [if_neg hsb] at hv
        contradiction

/-- Every vertex that touches a side during a sequence is part of the side's contamination afterwards. -/
theorem seq_touchers_subset_contam {V : Type*} {Γ : Type*} [DecidableEq Γ]
    (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V) (s : Γ × Bool) :
    seq_touchers seq s ⊆ seq_contam seq t s := by
  induction seq generalizing t with
  | nil =>
    intro v hv
    cases hv
  | cons h tl ih =>
    intro v hv
    cases hv with
    | inl htouch =>
      have h1 : v ∈ handshake_update_contam h t s :=
        seq_touchers_subset_contam_handshake_touchers_subset_contam_step h t s htouch
      exact seq_touchers_subset_contam_contam_subset_seq_contam tl (handshake_update_contam h t) s h1
    | inr hrest =>
      exact ih (handshake_update_contam h t) hrest
