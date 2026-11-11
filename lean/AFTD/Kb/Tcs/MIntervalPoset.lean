import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalPoset
import AFTD.Kb.Tcs.IsMIntervalPoset

/-!
# MIntervalPoset

Topic: combinatorics   Node: d5203eb749e0

Provenance: formalization of a published result. Source: arXiv:1311.3922 Def. 4.5

The type MIntervalPoset m n is the subtype of interval-posets on Fin (n * m) satisfying the m-synchronization condition.
-/

/-- The type of synchronized m-interval posets of size n. -/
abbrev MIntervalPoset (m n : ℕ) : Type := { P : IntervalPoset (Fin (n * m)) // is_m_interval_poset m n P }
