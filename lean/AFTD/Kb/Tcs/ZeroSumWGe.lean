import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumW
import AFTD.Kb.Tcs.ZeroSumBasisSeqWBad
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq
import AFTD.Kb.Tcs.ZeroSumWBad
import AFTD.Kb.Tcs.ZeroSumBasisSeq

/-!
# zero_sum_w_ge

Topic: combinatorics   Node: b05d9f581108

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Lemma 3.1 (consequence).

w_r(n) ≥ 2r(n−1) + 1 for all r ≥ 1 and n > 1.
-/

theorem zero_sum_w_ge (r n : ℕ) (hn : 1 < n) : ((2 * r * (n - 1) + 1 : ℕ) : ℕ∞) ≤ zero_sum_w r n := by
  unfold zero_sum_w
  refine le_iInf₂ (fun N hN => ?_)
  by_contra hlt
  rw [not_le] at hlt
  have hle : N ≤ 2 * r * (n - 1) := by
    have := (Nat.cast_lt (α := ℕ∞)).mp hlt
    omega
  obtain ⟨hbad, hlen⟩ := zero_sum_basis_seq_w_bad r n hn
  have htl : ((zero_sum_basis_seq r n).take N).length ≤ (zero_sum_basis_seq r n).length := by
    simp
  obtain ⟨I, hIne, hIdiv, j, hj⟩ := hN ((zero_sum_basis_seq r n).take N) (by simp [hlen]; omega)
    (fun a ha => hbad.1 a (List.mem_of_mem_take ha))
  have hsum : ∀ j, ∑ i ∈ I.map ⟨Fin.castLE htl, Fin.castLE_injective htl⟩,
      (zero_sum_basis_seq r n).get i j = ∑ i ∈ I, ((zero_sum_basis_seq r n).take N).get i j := by
    intro j
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [List.getElem_take]
  apply hbad.2 (I.map ⟨Fin.castLE htl, Fin.castLE_injective htl⟩)
  refine ⟨hIne.map, fun j => ?_, j, ?_⟩
  · rw [hsum]; exact hIdiv j
  · rw [hsum]; exact hj
