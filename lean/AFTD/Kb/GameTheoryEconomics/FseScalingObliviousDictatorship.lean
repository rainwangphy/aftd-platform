import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseSurjective
import AFTD.Kb.GameTheoryEconomics.FseDictatorship
import AFTD.Kb.GameTheoryEconomics.FseSPAll
import AFTD.Kb.GameTheoryEconomics.FsePath
import AFTD.Kb.GameTheoryEconomics.FseExistsAvoid
import AFTD.Kb.GameTheoryEconomics.FseMemRange
import AFTD.Kb.GameTheoryEconomics.FseFollow

/-!
# fse_scaling_oblivious_dictatorship

Topic: mechanism_design   Node: 8e9ede185c15

The dictatorship conjecture holds for scaling-oblivious mechanisms. If a mechanism into [0,1] does not depend on the scaling function and is strategyproof for every continuous positive scaling function, and it is surjective onto [0,1], then it is a dictatorship.
-/

/-- **The dictatorship conjecture holds for scaling-oblivious mechanisms.** If a mechanism into `[0,1]` does not depend on the scaling function and is strategyproof for every continuous positive scaling function, and it is surjective onto `[0,1]`, then it is a dictatorship. -/
theorem fse_scaling_oblivious_dictatorship {n : ℕ} [NeZero n] (f : (Fin n → ℝ) → ℝ)
    (hSP : fse_SPAll f) (hsurj : fse_Surjective f) : fse_Dictatorship f := by
  -- a profile with distinct coordinates
  let p0 : Fin n → ℝ := fun i => (i.val : ℝ) / n
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hp0 : fse_InDomain p0 := by
    intro i
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hn]; exact_mod_cast i.isLt.le
  have hp0inj : ∀ a b : Fin n, p0 a = p0 b → a = b := by
    intro a b h
    simp only [p0] at h
    rw [div_left_inj' hn.ne'] at h
    exact Fin.ext (by exact_mod_cast h)
  obtain ⟨istar, hstar⟩ := fse_mem_range f hSP hsurj p0 hp0
  refine ⟨istar, fun x hx => ?_⟩
  obtain ⟨t0, ht0, ht0n⟩ := fse_exists_avoid (Set.range x ∪ Set.range p0)
    ((Set.finite_range x).union (Set.finite_range p0))
  simp only [Set.mem_union, Set.mem_range, not_or, not_exists] at ht0n
  obtain ⟨hx0, hp00⟩ := ht0n
  -- step a: move agent istar to t0 in p0
  have ha : f (Function.update p0 istar t0) = t0 :=
    fse_follow f hSP hsurj p0 hp0 istar hstar
      (fun k hk h => hk (hp0inj k istar h)) t0 ht0
  -- step b: move all other agents to their x-locations
  have hz : fse_InDomain (Function.update x istar t0) := by
    intro k
    by_cases hk : k = istar
    · subst hk; simp [ht0]
    · simp [Function.update_of_ne hk, hx k]
  have hc1 : fse_InDomain (Function.update p0 istar t0) := by
    intro k
    by_cases hk : k = istar
    · subst hk; simp [ht0]
    · simp [Function.update_of_ne hk, hp0 k]
  have hb : f (Function.update x istar t0) = t0 := by
    apply fse_path f hSP _ _ hc1 hz t0 ha
    intro j hj
    by_cases hjs : j = istar
    · subst hjs; simp at hj
    · rw [Function.update_of_ne hjs]; exact fun h => hp00 j h
  -- step c: move agent istar back to x istar
  have hc := fse_follow f hSP hsurj (Function.update x istar t0) hz istar
    (by simp [hb]) (fun k hk => by
      rw [Function.update_of_ne hk, Function.update_self]; exact fun h => hx0 k h)
    (x istar) (hx istar)
  rw [Function.update_idem, Function.update_eq_self] at hc
  exact hc
