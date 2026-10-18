import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake

/-!
# handshake_edge

Topic: combinatorics   Node: c0513f1c1df5

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:154

The unordered edge in $\mathrm{Sym}^2(V)$ covered by a handshake between vertices $x$ and $y$, namely $s(x, y)$.
-/

/-- The edge covered by a handshake. -/
def handshake_edge {V : Type*} {Γ : Type*} (h : Handshake V Γ) : Sym2 V := match h with
  | .single x _ y => s(x, y)
  | .double x _ _ y => s(x, y)
