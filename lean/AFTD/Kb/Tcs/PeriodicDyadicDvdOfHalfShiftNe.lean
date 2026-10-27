import AFTD.Prelude

/-!
# periodic_dyadic_dvd_of_half_shift_ne

Topic: combinatorics   Node: d27f2e743410

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

If a function on the integers has periods n and 2^(m+1), and some values differ after shifting by 2^m, then 2^(m+1) divides n.
-/

open Finset

theorem periodic_dyadic_dvd_of_half_shift_ne
    {α : Type*} (m n : ℕ) (σ : ℤ → α)
    (hperiod : Function.Periodic σ (n : ℤ))
    (hdyadic : Function.Periodic σ ((2^(m+1) : ℕ) : ℤ))
    (hhalf : ∃ p : ℤ, σ (p + ((2^m : ℕ) : ℤ)) ≠ σ p) :
    2^(m+1) ∣ n := by
  let D := 2^(m+1)
  let H := 2^m
  by_contra hnd
  let g := Nat.gcd D n
  have hgD : g ∣ D := Nat.gcd_dvd_left D n
  have hgn : g ∣ n := Nat.gcd_dvd_right D n
  have hgH : g ∣ H := by
    obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgD
    have hk' : k ≤ m := by
      by_contra hn
      have hke : k = m+1 := by omega
      have hge : g = D := by simpa only [hke] using hg
      apply hnd
      change D ∣ n
      rw [← hge]
      exact hgn
    rw [hg]
    exact ⟨2^(m-k), by dsimp [H]; rw [← pow_add]; congr 1; omega⟩
  obtain ⟨w, hw⟩ := hgH
  have hb : ((Nat.gcd D n : ℕ) : ℤ) =
      D * Nat.gcdA D n + n * Nat.gcdB D n := Nat.gcd_eq_gcd_ab D n
  have hHz : (H : ℤ) =
      (Nat.gcdA D n * w) * (D : ℤ) +
        (Nat.gcdB D n * w) * (n : ℤ) := by
    calc
      (H : ℤ) = (g : ℤ)*(w : ℤ) := by exact_mod_cast hw
      _ = _ := by dsimp [g]; rw [hb]; ring
  have hpH : Function.Periodic σ (H : ℤ) := by
    rw [hHz]
    exact (hdyadic.int_mul (Nat.gcdA D n*w)).add_period
      (hperiod.int_mul (Nat.gcdB D n*w))
  obtain ⟨p, hp⟩ := hhalf
  exact hp (hpH p)
