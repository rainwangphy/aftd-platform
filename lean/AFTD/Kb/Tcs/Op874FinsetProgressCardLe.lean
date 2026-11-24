import AFTD.Prelude

/-!
# op874_finset_progress_card_le

Topic: graphs   Node: 9f3bc8083817

Provenance: helper lemma. OP-874: dense gadget obstruction to bounded component-switch repair, experiment 38459.

A process that starts with an empty finite set and adds at most one element at each step has at most n elements after n steps.
-/

theorem op874_finset_progress_card_le {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (n : ℕ) (h0 : S 0 = ∅)
    (hstep : ∀ i < n, ((S (i+1)) \ (S i)).card ≤ 1) :
    (S n).card ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hi : (S n).card ≤ n := ih (fun i hi => hstep i (by omega))
    have hs := hstep n (by omega)
    have hc := Finset.card_le_card_sdiff_add_card (s := S (n+1)) (t := S n)
    omega
