import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_ordered_shape_half

Topic: combinatorics   Node: 37bba6e5f515

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Twice the number of available unordered dimension pairs is at most one plus the number of ordered dimension pairs fitting in the square.
-/

theorem mondrian_ordered_shape_half (n A : ℕ) :
    2 * (mondrian_factor_shapes n A).card ≤
      (A.divisorsAntidiagonal.filter (fun d => d.1 ≤ n ∧ d.2 ≤ n)).card + 1 := by
  let S := mondrian_factor_shapes n A
  let T := S.map (Equiv.prodComm ℕ ℕ).toEmbedding
  let U := A.divisorsAntidiagonal.filter (fun d => d.1 ≤ n ∧ d.2 ≤ n)
  have hunion : S ∪ T = U := by
    ext d
    simp only [S, T, U, Finset.mem_union, Finset.mem_map,
      Equiv.prodComm_apply, Equiv.toEmbedding_apply,
      mondrian_mem_factor_shapes, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro (⟨hprod, hA, hord, hn⟩ | ⟨s, ⟨hprod, hA, hord, hn⟩, rfl⟩)
      · exact ⟨⟨hprod, hA⟩, hord.trans hn, hn⟩
      · exact ⟨⟨by simpa [Nat.mul_comm] using hprod, hA⟩, hn, hord.trans hn⟩
    · rintro ⟨⟨hprod, hA⟩, hx, hy⟩
      by_cases hxy : d.1 ≤ d.2
      · exact Or.inl ⟨hprod, hA, hxy, hy⟩
      · exact Or.inr ⟨d.swap, ⟨by simpa [Nat.mul_comm] using hprod, hA,
          by change d.2 ≤ d.1; omega, hx⟩,
          Prod.swap_swap d⟩
  have hint : (S ∩ T).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyS, hyT⟩ := Finset.mem_inter.mp hy
    obtain ⟨hxp, _, hxord, _⟩ := (mondrian_mem_factor_shapes n A x).mp hxS
    obtain ⟨hyp, _, hyord, _⟩ := (mondrian_mem_factor_shapes n A y).mp hyS
    obtain ⟨s, hs, hxs⟩ := Finset.mem_map.mp hxT
    obtain ⟨t, ht, hyt⟩ := Finset.mem_map.mp hyT
    have hsord := ((mondrian_mem_factor_shapes n A s).mp hs).2.2.1
    have htord := ((mondrian_mem_factor_shapes n A t).mp ht).2.2.1
    have hxeq : x.1 = x.2 := by
      have h1 := congrArg Prod.fst hxs
      have h2 := congrArg Prod.snd hxs
      dsimp at h1 h2
      omega
    have hyeq : y.1 = y.2 := by
      have h1 := congrArg Prod.fst hyt
      have h2 := congrArg Prod.snd hyt
      dsimp at h1 h2
      omega
    apply Prod.ext <;> nlinarith
  have hc := Finset.card_union_add_card_inter S T
  have hT : T.card = S.card := by simp [T]
  rw [hunion, hT] at hc
  dsimp [S, U] at hc hint
  omega
