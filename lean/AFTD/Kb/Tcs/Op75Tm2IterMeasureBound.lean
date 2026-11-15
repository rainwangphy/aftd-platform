import AFTD.Prelude

/-!
# op75_tm2_iter_measure_bound

Topic: np_completeness   Node: eb2338f13f95

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

If every transition of a partial state machine increases a natural-valued measure by at most C, then any n-step run increases it by at most C times n.
-/

theorem op75_tm2_iter_measure_bound {α : Type} (f : α → Option α) (measure : α → ℕ) (C : ℕ)
    (hstep : ∀ a b, f a = some b → measure b ≤ measure a + C)
    (n : ℕ) (a b : α)
    (h : ((fun o : Option α => o.bind f))^[n] (some a) = some b) :
    measure b ≤ measure a + C*n := by
  induction n generalizing b with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at h
      cases Option.some.inj h
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']  at h
      cases hp : ((fun o : Option α => o.bind f))^[n] (some a) with
      | none => simp [hp] at h
      | some mid =>
          have hm := ih mid hp
          have hf : f mid = some b := by simpa [hp] using h
          have hs := hstep mid b hf
          simp only [Nat.mul_succ]
          omega
