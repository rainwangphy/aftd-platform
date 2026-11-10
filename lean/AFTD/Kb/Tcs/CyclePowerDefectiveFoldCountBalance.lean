import AFTD.Prelude

/-!
# cycle_power_defective_fold_count_balance

Topic: combinatorics   Node: 88581bb015a8

Provenance: helper lemma. Defective half-model reduction for research thread RT-1.

Folding a defective model yields an exact identity relating folded count, lower-half counts and shifted defects.
-/

theorem cycle_power_defective_fold_count_balance
    (L k : ℕ) (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ)
    (hcount : ∀ v : ℤ, (Finset.range (L+L)).sum (fun a =>
      (y (v-(a : ℤ)) a).toNat) + (e v).toNat = k+1)
    (htop : ∀ v : ℤ, (Finset.range L).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+L)).toNat) + (e (v+shift)).toNat = 1) :
    ∀ v : ℤ,
      (Finset.range L).sum (fun a =>
        (y (v-(a : ℤ)) a || y (v-(a : ℤ)) (a+L)).toNat) +
      (Finset.range L).sum (fun a => (y (v+(L:ℤ)-(a:ℤ)) a).toNat) +
      (e (v+(L:ℤ))).toNat =
      (Finset.range L).sum (fun a => (y (v-(a:ℤ)) a).toNat) + k + (e (v+shift)).toNat := by
  intro v
  have hc := hcount (v+(L:ℤ))
  rw [Finset.sum_range_add] at hc
  have hB : (Finset.range L).sum (fun i =>
      (y (v+(L:ℤ)-((L+i:ℕ):ℤ)) (L+i)).toNat) =
      (Finset.range L).sum (fun a => (y (v-(a:ℤ)) (a+L)).toNat) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : v+(L:ℤ)-((L+i:ℕ):ℤ) = v-(i:ℤ) := by push_cast; ring
    rw [hp, Nat.add_comm L i]
  rw [hB] at hc
  have hF : (Finset.range L).sum (fun a =>
      (y (v-(a:ℤ)) a || y (v-(a:ℤ)) (a+L)).toNat) +
      (Finset.range L).sum (fun a =>
        (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+L)).toNat) =
      (Finset.range L).sum (fun a => (y (v-(a:ℤ)) a).toNat) +
      (Finset.range L).sum (fun a => (y (v-(a:ℤ)) (a+L)).toNat) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    cases y (v-(a:ℤ)) a <;> cases y (v-(a:ℤ)) (a+L) <;> rfl
  have hp := htop v
  omega
