import AFTD.Prelude

/-!
# cycle_power_fifteen_class_weight_certificate

Topic: combinatorics   Node: e717deef5dec

Provenance: helper lemma. Counting step for the k = 15 case of OP-205, arXiv:2610.15635. Experiment 3978 identifies the weights; the proof assigns one weighted edge to each vertex in a rooted forest.

For a subset of the sixteen positions of an arc, the weighted number of pairs at distances 8, 12, 14, 15, with weights 1, 1, 1, 2, is at most its cardinality.
-/

theorem cycle_power_fifteen_class_weight_certificate(b : Fin 16 → Bool) :
    2 * (b 0 && b 15).toNat +
      (∑ i : Fin 2, (b ⟨i.val, by omega⟩ && b ⟨i.val + 14, by omega⟩).toNat) +
      (∑ i : Fin 4, (b ⟨i.val, by omega⟩ && b ⟨i.val + 12, by omega⟩).toNat) +
      (∑ i : Fin 8, (b ⟨i.val, by omega⟩ && b ⟨i.val + 8, by omega⟩).toNat) ≤
      ∑ i : Fin 16, (b i).toNat := by
  have hl : ∀ x y : Bool, (x && y).toNat ≤ x.toNat := by decide
  have hr : ∀ x y : Bool, (x && y).toNat ≤ y.toNat := by decide
  have h0 := hl (b 0) (b 15)
  have h15 := hr (b 0) (b 15)
  have h14 := hr (b 0) (b 14)
  have h1 := hl (b 1) (b 15)
  have h12 := hr (b 0) (b 12)
  have h13 := hr (b 1) (b 13)
  have h2 := hl (b 2) (b 14)
  have h3 := hl (b 3) (b 15)
  have h8 := hr (b 0) (b 8)
  have h9 := hr (b 1) (b 9)
  have h10 := hr (b 2) (b 10)
  have h11 := hr (b 3) (b 11)
  have h4 := hl (b 4) (b 12)
  have h5 := hl (b 5) (b 13)
  have h6 := hl (b 6) (b 14)
  have h7 := hl (b 7) (b 15)
  norm_num [Fin.sum_univ_succ, Fin.succ_mk, Fin.reduceFinMk]
  change 2 * (b 0 && b 15).toNat + ((b 0 && b 14).toNat + ((b 1 && b 15).toNat)) + ((b 0 && b 12).toNat + ((b 1 && b 13).toNat + ((b 2 && b 14).toNat + ((b 3 && b 15).toNat)))) + ((b 0 && b 8).toNat + ((b 1 && b 9).toNat + ((b 2 && b 10).toNat + ((b 3 && b 11).toNat + ((b 4 && b 12).toNat + ((b 5 && b 13).toNat + ((b 6 && b 14).toNat + ((b 7 && b 15).toNat)))))))) ≤
    (b 0).toNat + ((b 1).toNat + ((b 2).toNat + ((b 3).toNat + ((b 4).toNat + ((b 5).toNat + ((b 6).toNat + ((b 7).toNat + ((b 8).toNat + ((b 9).toNat + ((b 10).toNat + ((b 11).toNat + ((b 12).toNat + ((b 13).toNat + ((b 14).toNat + ((b 15).toNat)))))))))))))))
  omega
