import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripWitness
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.PetersenStripVertex
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# petersen_strip_witness_card

Topic: graphs   Node: c1c3d3b579f9

Provenance: helper lemma. step towards petersen_strip_small_boundary_attainment

For each natural number k ≥ 8, the witness set petersen_strip_witness k has cardinality k^2/2 + 1.
-/

lemma petersen_strip_witness_card_disjoint_uv (U V : Finset ℤ) :
    Disjoint (Finset.image PetersenStripVertex.u U) (Finset.image PetersenStripVertex.v V) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
  injection hb

lemma petersen_strip_witness_card_witness_parts (U V : Finset ℤ) :
    (Finset.image PetersenStripVertex.u U ∪ Finset.image PetersenStripVertex.v V).card = U.card + V.card := by
  rw [Finset.card_union_of_disjoint (petersen_strip_witness_card_disjoint_uv U V)]
  have hu : Function.Injective PetersenStripVertex.u := by intro a b h; injection h
  have hv : Function.Injective PetersenStripVertex.v := by intro a b h; injection h
  rw [Finset.card_image_of_injective _ hu, Finset.card_image_of_injective _ hv]

lemma petersen_strip_witness_card_block (r k m : ℕ) :
    ((Finset.range m).image (fun (j : ℕ) => ((r * k + j : ℕ) : ℤ))).card = m := by
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range m
  · intro a b hab
    dsimp at hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)

lemma petersen_strip_witness_card_U_eq (k R m : ℕ) (hm : m ≤ k) :
    ((Finset.range R).biUnion (fun r => (Finset.range m).image (fun j => ((r * k + j : ℕ) : ℤ)))).card = R * m := by
  set t : ℕ → Finset ℤ := fun r => (Finset.range m).image fun j => ((r * k + j : ℕ) : ℤ)
  have ht_disj : (↑(Finset.range R) : Set ℕ).PairwiseDisjoint t := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.mem_coe, Finset.mem_range] at hr1 hr2
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨j1, hj1, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j2, hj2, heq⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hj1 hj2
    have h_eq : r1 * k + j1 = r2 * k + j2 := Nat.cast_injective heq.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : r1 * k + j1 < r2 * k + j2 := by nlinarith
      omega
    · have : r2 * k + j2 < r1 * k + j1 := by nlinarith
      omega
  have ht_card : ∀ r ∈ Finset.range R, (t r).card = m := by
    intro r _
    exact petersen_strip_witness_card_block r k m
  rw [Finset.card_biUnion ht_disj]
  have : (∑ u ∈ Finset.range R, (t u).card) = ∑ u ∈ Finset.range R, m := by
    apply Finset.sum_congr rfl ht_card
  rw [this, Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma petersen_strip_witness_card_extra_not_mem_U (k R m : ℕ) (hk : 8 ≤ k) :
    ((R : ℤ) * (k : ℤ) + (m : ℤ) - 1) ∉
      ((Finset.range R).biUnion (fun r => (Finset.range m).image (fun j => ((r * k + j : ℕ) : ℤ)))) := by
  intro hmem
  rw [Finset.mem_biUnion] at hmem
  rcases hmem with ⟨r, hr, hj⟩
  rw [Finset.mem_range] at hr
  rw [Finset.mem_image] at hj
  rcases hj with ⟨j, hj, heq⟩
  rw [Finset.mem_range] at hj
  have hr_le : (r : ℤ) ≤ (R : ℤ) - 1 := by omega
  have hj_le : (j : ℤ) ≤ (m : ℤ) - 1 := by omega
  have hk_ge : 8 ≤ (k : ℤ) := by omega
  have h_bound : ((r * k + j : ℕ) : ℤ) < (R : ℤ) * (k : ℤ) + (m : ℤ) - 1 := by
    push_cast
    nlinarith
  omega

lemma petersen_strip_witness_card_arithmetic (k : ℕ) :
    let m := k / 2
    let R := if (k % 2 == 0) = true then m else m + 1
    2 * R * m = k ^ 2 / 2 := by
  intro m R
  dsimp [R, m]
  split_ifs with h
  · rw [beq_iff_eq] at h
    have hk : k = 2 * (k / 2) := by omega
    conv_rhs => rw [hk]
    have : (2 * (k / 2)) ^ 2 = 2 * (2 * (k / 2) * (k / 2)) := by ring
    omega
  · rw [beq_iff_eq] at h
    have : k % 2 < 2 := Nat.mod_lt k (by decide)
    have hk : k = 2 * (k / 2) + 1 := by omega
    conv_rhs => rw [hk]
    have : (2 * (k / 2) + 1) ^ 2 = 2 * (2 * (k / 2 + 1) * (k / 2)) + 1 := by ring
    omega

/-- The finite witness set in the generalized Petersen strip has cardinality k^2 / 2 + 1 for all k ≥ 8. -/
theorem petersen_strip_witness_card (k : ℕ) (hk : 8 ≤ k) : (petersen_strip_witness k).card = k ^ 2 / 2 + 1 := by
  unfold petersen_strip_witness
  rw [petersen_strip_witness_card_witness_parts]
  set m := k / 2
  set R := if (k % 2 == 0) = true then m else m + 1
  set U : Finset ℤ := (Finset.range R).biUnion fun r => (Finset.range m).image fun j => ((r * k + j : ℕ) : ℤ)
  have h_not_mem : ((R : ℤ) * (k : ℤ) + (m : ℤ) - 1) ∉ U := petersen_strip_witness_card_extra_not_mem_U k R m hk
  rw [Finset.card_insert_of_notMem h_not_mem]
  have hm : m ≤ k := Nat.div_le_self k 2
  have hU : U.card = R * m := petersen_strip_witness_card_U_eq k R m hm
  rw [hU]
  have harith : 2 * R * m = k ^ 2 / 2 := petersen_strip_witness_card_arithmetic k
  rw [show R * m + (R * m + 1) = 2 * R * m + 1 by ring, harith]
