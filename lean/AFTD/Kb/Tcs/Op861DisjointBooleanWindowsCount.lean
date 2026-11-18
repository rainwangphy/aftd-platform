import AFTD.Prelude
import AFTD.Kb.Tcs.Op861BooleanWeightIntervalCount
import AFTD.Kb.Tcs.Op861BooleanRestrictionsInjective
import AFTD.Kb.Tcs.Op861BooleanBlockProductBound
import AFTD.Kb.Tcs.Op861BooleanMatchingWindowCount
import AFTD.Kb.Tcs.Op861BooleanBlockUniformBound
import AFTD.Kb.Tcs.Op861DisjointBooleanPartitionCard

/-!
# op861_disjoint_boolean_windows_count

Topic: graphs   Node: d646c2031f5d

Provenance: helper lemma. Finite independent-block small-ball counting step for op861_dense_triangle_orientation_sqrt_cover.

For a finite Boolean coordinate set, pairwise disjoint coordinate blocks, and integer offsets depending only on coordinates outside all blocks, the number of assignments satisfying one integer score window on each block, multiplied by the product of two to each block size, is at most two to the number of coordinates times the product over blocks of the window length times the largest binomial coefficient of that block size. Each score adds the offset to the number of bits matching a specified pattern.
-/

theorem op861_disjoint_boolean_windows_count (β ι : Type) [Fintype β]
    [DecidableEq β] [DecidableEq ι] (J : Finset ι) (B : ι → Finset β)
    (pattern : ι → β → Bool) (lo hi : ι → ℤ) (offset : ι → (β → Bool) → ℤ)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (B i) (B j))
    (hwindow : ∀ i ∈ J, lo i ≤ hi i)
    (hstable : ∀ i ∈ J, ∀ ω ω' : β → Bool,
      (∀ t, t ∉ J.biUnion B → ω t = ω' t) → offset i ω = offset i ω') :
    let score : ι → (β → Bool) → ℤ := fun i ω =>
      offset i ω + ∑ t ∈ B i, (if ω t = pattern i t then (1 : ℤ) else 0)
    ((Finset.univ : Finset (β → Bool)).filter (fun ω =>
      ∀ i ∈ J, lo i ≤ score i ω ∧ score i ω ≤ hi i)).card *
      (∏ i ∈ J, 2 ^ (B i).card) ≤
        2 ^ Fintype.card β *
          ∏ i ∈ J, ((hi i - lo i + 1).toNat * (B i).card.choose ((B i).card / 2)) := by
  classical
  intro score
  let ext : ({t : β // t ∉ J.biUnion B} → Bool) → β → Bool :=
    fun a t => if h : t ∉ J.biUnion B then a ⟨t, h⟩ else false
  let cnt : ∀ i : {i : ι // i ∈ J}, ({t : β // t ∈ B i.1} → Bool) → ℤ := fun i v =>
    (((Finset.univ : Finset {t : β // t ∈ B i.1}).filter (fun t => v t = pattern i.1 t.1)).card : ℤ)
  let P : ({t : β // t ∉ J.biUnion B} → Bool) →
      ∀ i : {i : ι // i ∈ J}, ({t : β // t ∈ B i.1} → Bool) → Prop :=
    fun a i v => lo i.1 ≤ offset i.1 (ext a) + cnt i v ∧ offset i.1 (ext a) + cnt i v ≤ hi i.1
  have hsum : ∀ (i : ι) (ω : β → Bool), ∑ t ∈ B i, (if ω t = pattern i t then (1 : ℤ) else 0)
      = (((Finset.univ : Finset {t : β // t ∈ B i}).filter
          (fun t => (fun t : {t : β // t ∈ B i} => ω t.1) t = pattern i t.1)).card : ℤ) := by
    intro i ω
    rw [← Finset.sum_coe_sort (B i), Finset.sum_boole]
  have hext : ∀ i ∈ J, ∀ ω : β → Bool, offset i (ext (fun t => ω t.1)) = offset i ω := by
    intro i hi ω
    apply hstable i hi
    intro t ht
    simp only [ext, dif_pos ht]
  have key := op861_boolean_block_uniform_bound β ι J B
    (fun ω => ∀ i ∈ J, lo i ≤ score i ω ∧ score i ω ≤ hi i) P
    (fun i => (hi i - lo i + 1).toNat * (B i).card.choose ((B i).card / 2))
    (by
      intro ω hω i
      have h := hω i.1 i.2
      simp only [score, hsum] at h
      simp only [P, cnt]
      rw [hext i.1 i.2 ω]
      exact h)
    (by
      intro a i
      have := op861_boolean_matching_window_count {t : β // t ∈ B i.1} (fun t => pattern i.1 t.1)
        (lo i.1) (hi i.1) (offset i.1 (ext a)) (hwindow i.1 i.2)
      rw [Fintype.card_coe] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, cnt])
  have hprod : (∏ i : {i : ι // i ∈ J},
      (hi i.1 - lo i.1 + 1).toNat * (B i.1).card.choose ((B i.1).card / 2))
      = ∏ i ∈ J, ((hi i - lo i + 1).toNat * (B i).card.choose ((B i).card / 2)) :=
    Finset.prod_coe_sort J (fun i => (hi i - lo i + 1).toNat * (B i).card.choose ((B i).card / 2))
  rw [hprod] at key
  have hpart := op861_disjoint_boolean_partition_card β ι J B hdisj
  calc _ ≤ (Fintype.card ({t : β // t ∉ J.biUnion B} → Bool) *
        ∏ i ∈ J, ((hi i - lo i + 1).toNat * (B i).card.choose ((B i).card / 2))) *
          (∏ i ∈ J, 2 ^ (B i).card) := Nat.mul_le_mul_right _ key
    _ = _ := by rw [← hpart]; ring
