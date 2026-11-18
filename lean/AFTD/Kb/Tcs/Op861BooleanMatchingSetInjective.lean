import AFTD.Prelude

/-!
# op861_boolean_matching_set_injective

Topic: graphs   Node: 6570149eaa22

Provenance: helper lemma. Per-block estimate for op861_disjoint_boolean_windows_count.

A Boolean assignment is uniquely determined by the set of positions where it matches a fixed Boolean pattern.
-/

theorem op861_boolean_matching_set_injective (β : Type*) [Fintype β] [DecidableEq β]
    (pattern : β → Bool) : Function.Injective
      (fun v : β → Bool => Finset.univ.filter (fun t => v t = pattern t)) := by
  classical
  intro v w h
  funext t
  have hm := congrArg (fun X : Finset β => t ∈ X) h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  cases hv : v t <;> cases hw : w t <;> cases hp : pattern t <;> simp_all
