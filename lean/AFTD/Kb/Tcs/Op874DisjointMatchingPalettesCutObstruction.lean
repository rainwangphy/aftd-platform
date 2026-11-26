import AFTD.Prelude
import AFTD.Kb.Tcs.Op874DisjointMatchingPalettesForceBadSameBitEdge

/-!
# op874_disjoint_matching_palettes_cut_obstruction

Topic: graphs   Node: 84af744dc0d9

Provenance: helper lemma. Disjoint matching-palette obstruction for OP-874; https://arxiv.org/abs/2610.41950.

On the displayed eight-vertex matching and cut, no properly colored factor can have disjoint high palettes at every matching edge together with compatible local states.
-/

theorem op874_disjoint_matching_palettes_cut_obstruction :
    let mate : Fin 8 → Fin 8 := ![6,4,7,5,1,3,0,2]
    let bit : Fin 8 → Bool := ![true,false,false,true,false,true,true,false]
    ¬ ∃ (w : Fin 8 → Fin 4) (h : Fin 8 → Fin 3 → Fin 6),
      (∀ v, w (v-1) ≠ w v) ∧
      (∀ v, Function.Injective ![w (v-1),w v,w (mate v-1),w (mate v)]) ∧
      (∀ v i j, i ≠ j → h v i ≠ h v j) ∧
      (∀ v i, h v i ≠ (if bit v then 5 else 4)) ∧
      (∀ v i, h v i ≠ Fin.castAdd 2 (w (v-1))) ∧
      (∀ v i, h v i ≠ Fin.castAdd 2 (w v)) ∧
      (∀ v i j, i ≠ 1 → j ≠ 0 → h v i ≠ h (v+1) j) := by
  intro mate bit hex
  obtain ⟨w,h,hproper,hmatch,hpair,hlow,hprev,hnext,hcompat⟩ := hex
  have ha : Function.Injective ![w 1,w 2,w 6,w 7] := by
    simpa [mate] using hmatch 2
  have hb : Function.Injective ![w 5,w 6,w 7,w 0] := by
    have hm : (-1 : Fin 8) = 7 := by decide
    simpa [mate, hm] using hmatch 6
  have hp : w 0 ≠ w 1 := by simpa using hproper 1
  have hx : h 1 0 ≠ 4 ∧ h 1 0 ≠ Fin.castAdd 2 (w 0) ∧
      h 1 0 ≠ Fin.castAdd 2 (w 1) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [bit] using hlow 1 0
    · simpa using hprev 1 0
    · exact hnext 1 0
  have hy : h 1 2 ≠ 4 ∧ h 1 2 ≠ Fin.castAdd 2 (w 0) ∧
      h 1 2 ≠ Fin.castAdd 2 (w 1) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [bit] using hlow 1 2
    · simpa using hprev 1 2
    · exact hnext 1 2
  have hu : h 2 1 ≠ 4 ∧ h 2 1 ≠ Fin.castAdd 2 (w 2) ∧
      h 2 1 ≠ Fin.castAdd 2 (w 1) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [bit] using hlow 2 1
    · exact hnext 2 1
    · simpa using hprev 2 1
  have hv : h 2 2 ≠ 4 ∧ h 2 2 ≠ Fin.castAdd 2 (w 2) ∧
      h 2 2 ≠ Fin.castAdd 2 (w 1) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [bit] using hlow 2 2
    · exact hnext 2 2
    · simpa using hprev 2 2
  have hxy : h 1 0 ≠ h 1 2 := hpair 1 0 2 (by decide)
  have huv : h 2 1 ≠ h 2 2 := hpair 2 1 2 (by decide)
  have hd : h 1 0 ≠ h 2 1 ∧ h 1 0 ≠ h 2 2 ∧
      h 1 2 ≠ h 2 1 ∧ h 1 2 ≠ h 2 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hcompat 1 0 1 (by decide) (by decide)
    · simpa using hcompat 1 0 2 (by decide) (by decide)
    · simpa using hcompat 1 2 1 (by decide) (by decide)
    · simpa using hcompat 1 2 2 (by decide) (by decide)
  exact op874_disjoint_matching_palettes_force_bad_same_bit_edge
    w ha hb hp (h 1 0) (h 1 2) (h 2 1) (h 2 2) hx hy hu hv hxy huv hd
