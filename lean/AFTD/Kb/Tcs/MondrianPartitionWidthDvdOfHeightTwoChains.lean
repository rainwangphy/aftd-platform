import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionWidthFreeHeightSignedRelation
import AFTD.Kb.Tcs.MondrianTwoChainSignedSumNeZero
import AFTD.Kb.Tcs.MondrianPerfectHeightInjective
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_partition_width_dvd_of_height_two_chains

Topic: combinatorics   Node: 2ea6b271765c

Provenance: helper lemma. For the three-prime extension of OP-280, arXiv:2610.19193, Section 1. This develops the proved mondrian_no_perfect_two_prime_area and the width-free signed-height relation from this session.

If d divides the square side and all width-indivisible tiles have heights in two superincreasing chains C*p^a and C*r*p^a, with p>r+1 and r≥2, then every tile width is divisible by d.
-/

theorem mondrian_partition_width_dvd_of_height_two_chains (n d p r C : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) (hdn : d ∣ n) (hC : 0 < C)
    (hr : 2 ≤ r) (hpr : r + 1 < p)
    (hheight : ∀ u ∈ P, ¬ d ∣ mondrian_rect_width u → ∃ a : ℕ,
      mondrian_rect_height u = C * p ^ a ∨ mondrian_rect_height u = C * r * p ^ a) :
    ∀ u ∈ P, d ∣ mondrian_rect_width u := by
  classical
  intro u hu
  by_contra hfree
  obtain ⟨L, hLnd, hLmem, hLsum⟩ :=
    mondrian_partition_width_free_height_signed_relation n d P hP hdn u hu hfree
  let H := (mondrian_rect_height u, false) ::
    L.map (fun t => (mondrian_rect_height t.1, t.2))
  have hhnd : (L.map (fun t => mondrian_rect_height t.1)).Nodup := by
    have hh : ((L.map Prod.fst).map mondrian_rect_height).Nodup := by
      apply List.Nodup.map_on _ hLnd
      intro v hv w hw he
      obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hv
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      exact mondrian_perfect_height_injective n P hP hz v'.1 (hLmem v' hv').1
        w'.1 (hLmem w' hw').1 he
    simpa only [List.map_map, Function.comp_def] using hh
  have hhead : mondrian_rect_height u ∉ L.map (fun t => mondrian_rect_height t.1) := by
    intro hm
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    exact (hLmem t ht).2.1 (mondrian_perfect_height_injective n P hP hz
      t.1 (hLmem t ht).1 u hu he)
  have hnd : (H.map Prod.fst).Nodup := by
    simpa only [H, List.map_cons, List.map_map, Function.comp_def] using
      (List.nodup_cons.mpr ⟨hhead, hhnd⟩)
  have hrep : ∀ t ∈ H, ∃ a : ℕ, t.1 = C * p ^ a ∨ t.1 = C * r * p ^ a := by
    intro t ht
    rcases List.mem_cons.mp ht with he | ht
    · subst t
      exact hheight u hu hfree
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      exact hheight v.1 (hLmem v hv).1 (hLmem v hv).2.2
  have hzero : (H.map (fun t => if t.2 then (t.1 : ℤ) else -(t.1 : ℤ))).sum = 0 := by
    simp only [H, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      Bool.false_eq_true, if_false]
    rw [hLsum]
    ring
  exact mondrian_two_chain_signed_sum_ne_zero p r C hC hr hpr H (by simp [H]) hnd hrep hzero
