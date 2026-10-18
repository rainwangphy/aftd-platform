import AFTD.Prelude

/-!
# DeadlineRequest

Topic: online_algorithms   Node: 2957e16c3f8f

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

A request in online paging with deadlines, specifying a requested page in α, an arrival time in ℕ, and a deadline in ℕ with arrival ≤ deadline.
-/

/-- A request in online paging with deadlines. -/
structure DeadlineRequest (α : Type*) where
  page : α
  arrival : ℕ
  deadline : ℕ
  h_deadline : arrival ≤ deadline
