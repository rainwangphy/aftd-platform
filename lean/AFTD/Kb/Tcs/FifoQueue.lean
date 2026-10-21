import AFTD.Prelude

/-!
# FifoQueue

Topic: online_algorithms   Node: 1f0d26d90bed

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.1

A first-in first-out (FIFO) cache queue of capacity k over page type α, represented as a duplicate-free list of length k.
-/

/-- A FIFO cache queue of capacity k storing k distinct pages. -/
structure FifoQueue (α : Type*) (k : ℕ) where
  pages : List α
  length_eq : pages.length = k
  nodup : pages.Nodup
