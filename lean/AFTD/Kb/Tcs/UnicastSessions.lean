import AFTD.Prelude

/-!
# UnicastSessions

Topic: information   Node: 2cbca012eafd

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

A collection of unicast communication sessions indexed by a type K on an arbitrary vertex type V, consisting of a source map src : K → V, a target map tgt : K → V, and a proof that src k ≠ tgt k for every k : K.
-/

/-- A collection of unicast communication sessions with distinct source and sink vertices. -/
structure UnicastSessions (V : Type) (K : Type) where
  src : K → V
  tgt : K → V
  src_ne_tgt : ∀ k, src k ≠ tgt k
