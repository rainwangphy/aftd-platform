import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalCrossingEvenShoreCoversOppositeFirstSide
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_first_bridge_second_shore_does_not_cross

Topic: graphs   Node: 2c5686f590d7

Provenance: helper lemma. OP-1957 crossing-cut consequence of the first forced edge and factor-critical parity.

In the factor-critical first-bridge configuration, a nonempty matching-compatible second bridge shore cannot meet both first shores, regardless of the codegree of its endpoint.
-/

theorem factorcritical_first_bridge_second_shore_does_not_cross (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj] (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v : Fin (2*k+d+3)) (hxy : x ≠ y) (huv : ¬ H.Adj u v) (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y) (A B Q W : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B) (hxu : x ∉ A ∪ B) (hyu : y ∉ A ∪ B) (hqx : x ∉ Q) (hqy : y ∉ Q) (hu : u ∈ A) (hv : v ∈ B) (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b) (hwsub : W ⊆ A ∪ B) (hwne : W.Nonempty) (hqne : Q.Nonempty) (hevenA : Even (W ∩ A).card) (hevenB : Even (W ∩ B).card) (hsize : Q.card + W.card = d+1) (hxyW : ∀ w ∈ W, H.Adj x w ∧ H.Adj y w) (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : Disjoint W A ∨ Disjoint W B := by
  classical
  by_cases hWA : Disjoint W A
  · exact Or.inl hWA
  by_cases hWB : Disjoint W B
  · exact Or.inr hWB
  exfalso
  have hneA : (W ∩ A).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hWA
  have hneB : (W ∩ B).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hWB
  have hbcover := factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y u v hxy A B Q W hAB hxu hyu hqx hqy hu hv hcut hwsub hevenA hneA hsize hxyW hcross
  have hcut' : ∀ b ∈ B, ∀ a ∈ A, (b ≠ v ∨ a ≠ u) → H.Adj b a := by
    intro b hb a ha h
    apply (hcut a ha b hb ?_).symm
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hacover := factorcritical_crossing_even_shore_covers_opposite_first_side k d H hcrit x y v u hxy B A Q W hAB.symm
    (by simpa [Finset.union_comm] using hxu) (by simpa [Finset.union_comm] using hyu)
    hqx hqy hv hu hcut' (by simpa [Finset.union_comm] using hwsub) hevenB hneB hsize hxyW hcross
  have huWQ := Finset.mem_union.mp (hacover hu)
  have hvWQ := Finset.mem_union.mp (hbcover hv)
  rcases huWQ with huW | huQ <;> rcases hvWQ with hvW | hvQ
  · obtain ⟨q,hq⟩ := hqne
    have h := hcommon q (hcross q hq u huW).symm (hcross q hq v hvW).symm
    rcases h with rfl | rfl
    · exact hqx hq
    · exact hqy hq
  · exact huv (hcross v hvQ u huW).symm
  · exact huv (hcross u huQ v hvW)
  · obtain ⟨w,hw⟩ := hwne
    have h := hcommon w (hcross u huQ w hw) (hcross v hvQ w hw)
    rcases h with rfl | rfl
    · exact hxu (hwsub hw)
    · exact hyu (hwsub hw)
