import AFTD.Prelude

/-!
# op861_partition_profile_obstruction

Topic: graphs   Node: 8da82906ccd9

Provenance: helper lemma. Numerical counting step for the OP-861 two-block eligibility obstruction.

Numerical coverage and disjointness conditions for two palette-block profiles are inconsistent. The four count functions represent eligible colors in each block on each side; the first-transition argument yields incompatible eligible counts.
-/

theorem op861_partition_profile_obstruction (k p q : ℕ)
    (hp : 1 ≤ p) (hpk : p < k) (hpq : p + q + 1 = 2 * k)
    (ap aq bp bq : ℕ → ℕ)
    (hbound : ∀ x ≤ p, ap x ≤ p ∧ bp x ≤ p)
    (ha : ∀ x ≤ p, p + 1 ≤ ap x + x ∨ q + 1 + x ≤ aq x + k)
    (hb : ∀ x ≤ p, p + 1 ≤ bp x + x ∨ q + 1 + x ≤ bq x + k)
    (hqsep : ∀ x z, x ≤ p → z ≤ p → x + z = p → aq x + bq z ≤ q)
    (hpsep : ∀ x z, x ≤ p → z ≤ p → x + z = p + 1 → ap x + bp z ≤ p) : False := by
  have hzero : 0 ≤ p := Nat.zero_le _
  have hpair := hqsep p 0 le_rfl hzero (by omega)
  have hbound0 := hbound 0 hzero
  have hbq : q + 1 ≤ bq 0 + k := by
    rcases hb 0 hzero with h | h
    · omega
    · simpa using h
  have haplast : p + 1 ≤ ap p + p := by
    rcases ha p le_rfl with h | h
    · exact h
    · omega
  have hex : ∃ x, x ≤ p ∧ p + 1 ≤ ap x + x := ⟨p, le_rfl, haplast⟩
  let x := Nat.find hex
  have hx : x ≤ p ∧ p + 1 ≤ ap x + x := Nat.find_spec hex
  have hxpos : 0 < x := by
    by_contra hn
    have : x = 0 := by omega
    rw [this] at hx
    omega
  have hprev : ¬ (x - 1 ≤ p ∧ p + 1 ≤ ap (x - 1) + (x - 1)) :=
    Nat.find_min hex (by omega)
  have hprevlt : x - 1 ≤ p := by omega
  have haq : q + x ≤ aq (x - 1) + k := by
    rcases ha (x-1) hprevlt with h | h
    · exact False.elim (hprev ⟨hprevlt, h⟩)
    · omega
  have hzlt : p - x + 1 ≤ p := by omega
  have hcross := hqsep (x-1) (p-x+1) hprevlt hzlt (by omega)
  have hbp : x ≤ bp (p-x+1) := by
    rcases hb (p-x+1) hzlt with h | h
    · omega
    · omega
  have hlastcross := hpsep x (p-x+1) hx.1 hzlt (by omega)
  omega
