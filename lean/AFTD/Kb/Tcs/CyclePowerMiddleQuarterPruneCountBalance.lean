import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_middle_quarter_prune_count_balance

Topic: combinatorics   Node: d7c4cdef9098

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

For a four-quarter class model with parent implications, constant original active count t+1, and exact half-distance coverage, pruning gives C_pruned(v)+R(v)=t+R(v+H).
-/

open Finset

theorem cycle_power_middle_quarter_prune_count_balance
    (q t : ℕ) (x : ℤ → ℕ → Bool)
    (hleft : ∀ (p : ℤ) (a : ℕ), q ≤ a → a < 2 * q →
      x p a = true → x p (a + 2 * q) = true)
    (hright : ∀ (p : ℤ) (a : ℕ), 2 * q ≤ a → a < 3 * q →
      x p a = true → x p (a - 2 * q) = true)
    (hcount : ∀ v : ℤ, (range (4 * q)).sum
      (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1)
    (hhalf : ∀ v : ℤ, (range (2 * q)).sum
      (fun a => (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 * q)).toNat) = 1) :
    ∀ v : ℤ,
      (range (2 * q)).sum (fun a =>
        ((if a < q then x (v - (a : ℤ)) a else
          x (v - (a : ℤ)) (a + 2 * q)) : Bool).toNat) +
      (range (2 * q)).sum (fun a =>
        (x (v - ((2 * q + a : ℕ) : ℤ)) (2 * q + a)).toNat) =
      t + (range (2 * q)).sum (fun a =>
        (x (v - (a : ℤ)) (2 * q + a)).toNat) := by
  intro v
  have htwo (f : ℕ → ℕ) :
      (range (2 * q)).sum f = (range q).sum f +
        (range q).sum (fun a => f (q + a)) := by
    simpa only [two_mul] using (sum_range_add f q q)
  have handr (a b : Bool) (h : b = true → a = true) :
      (a && b).toNat = b.toNat := by
    cases a <;> cases b <;> simp_all
  have handl (a b : Bool) (h : a = true → b = true) :
      (a && b).toNat = a.toNat := by
    cases a <;> cases b <;> simp_all
  let A := (range q).sum (fun a => (x (v - (a : ℤ)) a).toNat)
  let B := (range q).sum (fun a => (x (v - ((q + a : ℕ) : ℤ)) (q + a)).toNat)
  let C := (range q).sum (fun a => (x (v - ((2 * q + a : ℕ) : ℤ)) (2 * q + a)).toNat)
  let D := (range q).sum (fun a =>
    (x (v - ((2 * q + (q + a) : ℕ) : ℤ)) (2 * q + (q + a))).toNat)
  let E := (range q).sum (fun a => (x (v - (a : ℤ)) (2 * q + a)).toNat)
  let F := (range q).sum (fun a =>
    (x (v - ((q + a : ℕ) : ℤ)) (2 * q + (q + a))).toNat)
  have hfull : A + B + C + D = t + 1 := by
    have hh := hcount v
    have hs := cycle_power_dyadic_sum_range_four_blocks q
      (fun a => (x (v - (a : ℤ)) a).toNat)
    change (range (4 * q)).sum (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1 at hh
    rw [hs] at hh
    have hD : D = (range q).sum (fun a =>
        (x (v - ((3 * q + a : ℕ) : ℤ)) (3 * q + a)).toNat) := by
      apply sum_congr rfl
      intro a ha
      rw [show 2 * q + (q + a) = 3 * q + a by omega]
    rw [hD]
    exact hh
  have hmid : E + B = 1 := by
    have hh := hhalf v
    rw [htwo] at hh
    have hfirst :
        (range q).sum (fun a =>
          (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 * q)).toNat) = E := by
      apply sum_congr rfl
      intro a ha
      have haq : a < q := mem_range.mp ha
      have hp : x (v - (a : ℤ)) (a + 2 * q) = true →
          x (v - (a : ℤ)) a = true := by
        intro hx
        have hh := hright (v - (a : ℤ)) (a + 2 * q) (by omega) (by omega) hx
        simpa only [Nat.add_sub_cancel_right] using hh
      simpa only [Nat.add_comm a (2 * q)] using handr _ _ hp
    have hsecond :
        (range q).sum (fun a =>
          (x (v - ((q + a : ℕ) : ℤ)) (q + a) &&
            x (v - ((q + a : ℕ) : ℤ)) (q + a + 2 * q)).toNat) = B := by
      apply sum_congr rfl
      intro a ha
      have haq : a < q := mem_range.mp ha
      exact handl _ _ (hleft _ _ (by omega) (by omega))
    rw [hfirst, hsecond] at hh
    exact hh
  have hprune :
      (range (2 * q)).sum (fun a =>
        ((if a < q then x (v - (a : ℤ)) a else
          x (v - (a : ℤ)) (a + 2 * q)) : Bool).toNat) = A + F := by
    rw [htwo]
    congr 1
    · apply sum_congr rfl
      intro a ha
      rw [if_pos (mem_range.mp ha)]
    · apply sum_congr rfl
      intro a ha
      rw [if_neg (by omega : ¬q + a < q)]
      change (x (v - ((q + a : ℕ) : ℤ)) (q + a + 2 * q)).toNat =
        (x (v - ((q + a : ℕ) : ℤ)) (2 * q + (q + a))).toNat
      rw [show q + a + 2 * q = 2 * q + (q + a) by omega]
  have hrightcount : (range (2 * q)).sum (fun a =>
      (x (v - ((2 * q + a : ℕ) : ℤ)) (2 * q + a)).toNat) = C + D := htwo _
  have hshiftcount : (range (2 * q)).sum (fun a =>
      (x (v - (a : ℤ)) (2 * q + a)).toNat) = E + F := htwo _
  rw [hprune, hrightcount, hshiftcount]
  omega
