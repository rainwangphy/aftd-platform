import AFTD.Prelude

/-!
# Handshake

Topic: combinatorics   Node: 3413daf5b10f

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:154

A handshake between vertices in $V$ using gloves from $\Gamma$, which is either single-gloved (one vertex wears a glove side inside, the other is bare-handed) or double-gloved (each vertex wears a glove side inside, and the outer sides touch).
-/

/-- A single-gloved or double-gloved handshake between two players. -/
inductive Handshake (V : Type*) (Γ : Type*) where
  | single (x : V) (a : Γ × Bool) (y : V) : Handshake V Γ
  | double (x : V) (a : Γ × Bool) (b : Γ × Bool) (y : V) : Handshake V Γ
