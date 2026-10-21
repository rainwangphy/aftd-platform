import AFTD.Prelude
import AFTD.Kb.Tcs.PaymentWindow

/-!
# PagingWithDelayExecution

Topic: online_algorithms   Node: 90b7f987b38a

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 2 & Section 3

A structure PagingWithDelayExecution parameterized by page type α with decidable equality and cache capacity k : ℕ, consisting of the number of payments P : ℕ, offline fetch count F_opt : ℕ, offline delay D_opt : ℝ with 0 ≤ D_opt, a list of payment windows of length P, and an accounting property that (P : ℝ) ≤ (k + 1 : ℝ) * ((F_opt : ℝ) + D_opt).
-/

/-- Execution of 1-FIFO and offline algorithm for paging with delay. -/
structure PagingWithDelayExecution (α : Type*) [DecidableEq α] (k : ℕ) where
  P : ℕ
  F_opt : ℕ
  D_opt : ℝ
  h_delay_nonneg : 0 ≤ D_opt
  windows : List (PaymentWindow α k)
  h_windows_len : windows.length = P
  h_accounting : (P : ℝ) ≤ (k + 1 : ℝ) * ((F_opt : ℝ) + D_opt)
