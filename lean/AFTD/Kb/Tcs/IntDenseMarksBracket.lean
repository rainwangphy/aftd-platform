import AFTD.Prelude

/-!
# int_dense_marks_bracket

Topic: combinatorics   Node: 139ba2140dd1

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

If every integer lies at distance less than D after a marked integer, every unmarked integer lies strictly between two marked integers whose total separation is at most D.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem int_dense_marks_bracket
    (D : ℕ) (F : ℤ → Prop)
    (hdense : ∀ v : ℤ, ∃ a : ℕ, a < D ∧ F (v-(a : ℤ)))
    (p : ℤ) (hp : ¬F p) :
    ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ l+r ≤ D ∧ F (p-(l : ℤ)) ∧ F (p+(r : ℤ)) := by
  classical
  let S : Finset ℕ := (range D).filter (fun (a : ℕ) => F (p-(a : ℤ)))
  have hS : S.Nonempty := by
    obtain ⟨a, ha, hFa⟩ := hdense p
    exact ⟨a, mem_filter.mpr ⟨mem_range.mpr ha, hFa⟩⟩
  let l : ℕ := S.min' hS
  have hlmem : l ∈ S := min'_mem _ hS
  have hlD : l < D := mem_range.mp (mem_filter.mp hlmem).1
  have hFl : F (p-(l : ℤ)) := (mem_filter.mp hlmem).2
  have hl₀ : 0 < l := by
    by_contra hn
    have he : l = 0 := by omega
    exact hp (by simpa only [he, Nat.cast_zero, sub_zero] using hFl)
  let T : Finset ℕ := (range (D+1)).filter (fun (r : ℕ) => 0 < r ∧ F (p+(r : ℤ)))
  have hT : T.Nonempty := by
    obtain ⟨a, ha, hFa⟩ := hdense (p+(D : ℤ))
    have hroot : p+((D-a : ℕ) : ℤ) = p+(D : ℤ)-(a : ℤ) := by omega
    refine ⟨D-a, mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, ?_⟩⟩
    simpa only [hroot] using hFa
  let r : ℕ := T.min' hT
  have hrmem : r ∈ T := min'_mem _ hT
  have hr₀ : 0 < r := (mem_filter.mp hrmem).2.1
  have hFr : F (p+(r : ℤ)) := (mem_filter.mp hrmem).2.2
  obtain ⟨a, ha, hFa⟩ := hdense (p-(l : ℤ)+(D : ℤ))
  have hla : l+a < D := by
    by_contra hn
    let c := l+a-D
    have hcD : c < D := by dsimp [c]; omega
    have hcl : c < l := by dsimp [c]; omega
    have hcroot : p-(c : ℤ) = p-(l : ℤ)+(D : ℤ)-(a : ℤ) := by dsimp [c]; omega
    have hcmem : c ∈ S := mem_filter.mpr ⟨mem_range.mpr hcD, by simpa only [hcroot] using hFa⟩
    have hmin : l ≤ c := min'_le S c hcmem
    omega
  let t := D-l-a
  have ht₀ : 0 < t := by dsimp [t]; omega
  have htD : t < D+1 := by dsimp [t]; omega
  have htroot : p+(t : ℤ) = p-(l : ℤ)+(D : ℤ)-(a : ℤ) := by dsimp [t]; omega
  have htmem : t ∈ T := mem_filter.mpr ⟨mem_range.mpr htD, ht₀, by simpa only [htroot] using hFa⟩
  have hrt : r ≤ t := min'_le T t htmem
  exact ⟨l, r, hl₀, hr₀, by dsimp [t] at hrt; omega, hFl, hFr⟩
