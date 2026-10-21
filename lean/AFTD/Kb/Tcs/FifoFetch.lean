import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue

/-!
# fifo_fetch

Topic: online_algorithms   Node: 211142e15d4e

Provenance: formalization of a published result. Source: arXiv:2610.18767 Section 3.1

Updating a FIFO queue of size k ≥ 1 upon fetching a new page v: the oldest page (front of the queue) is evicted and v is appended to the back.
-/

/-- FIFO queue update upon fetching a page: evict head, append to tail. -/
def fifo_fetch {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages) : FifoQueue α k :=
  have hlen : q.pages.length = k := q.length_eq
  have h_ne : q.pages ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  match h_cons : q.pages with
  | [] => False.elim (h_ne h_cons)
  | head :: tail =>
    { pages := tail ++ [v]
      length_eq := by
        have h1 : (head :: tail).length = k := by rw [← h_cons, hlen]
        simp only [List.length_cons] at h1
        simp only [List.length_append, List.length_singleton]
        omega
      nodup := by
        have hnd : (head :: tail).Nodup := by rw [← h_cons]; exact q.nodup
        rw [List.nodup_cons] at hnd
        rw [List.nodup_append]
        refine ⟨hnd.2, List.nodup_singleton v, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        intro heq; subst heq
        have : x ∈ q.pages := by rw [h_cons]; exact List.mem_cons_of_mem head hx
        exact hv this }
