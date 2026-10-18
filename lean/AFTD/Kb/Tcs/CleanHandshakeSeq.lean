import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.HandshakeUpdateContam

/-!
# CleanHandshakeSeq

Topic: combinatorics   Node: 442f1a01dbaf

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:222

Inductive predicate stating that a sequence of handshakes is clean when executed starting from an initial contamination map $t$.
-/

/-- Predicate asserting a sequence of handshakes is clean starting from a contamination state. -/
inductive CleanHandshakeSeq {V : Type*} {Γ : Type*} [DecidableEq Γ] : List (Handshake V Γ) → (Γ × Bool → Set V) → Prop where
  | nil (t : Γ × Bool → Set V) : CleanHandshakeSeq [] t
  | cons (h : Handshake V Γ) (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V) :
      handshake_is_clean h t → CleanHandshakeSeq seq (handshake_update_contam h t) →
        CleanHandshakeSeq (h :: seq) t
