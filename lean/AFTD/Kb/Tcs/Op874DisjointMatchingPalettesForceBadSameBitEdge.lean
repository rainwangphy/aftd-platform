import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ContractionForcesEqualFactorPalette
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor

/-!
# op874_disjoint_matching_palettes_force_bad_same_bit_edge

Topic: graphs   Node: 62cb9b0fe730

Provenance: helper lemma. Disjoint matching-palette obstruction for OP-874; https://arxiv.org/abs/2610.41950.

For the displayed factor interfaces, two disjoint matching palettes force equal external color triples on a same-bit factor edge, contradicting local exposed-pair compatibility.
-/

theorem op874_disjoint_matching_palettes_force_bad_same_bit_edge
    (w : Fin 8 → Fin 4)
    (h27 : Function.Injective ![w 1,w 2,w 6,w 7])
    (h60 : Function.Injective ![w 5,w 6,w 7,w 0])
    (hp : w 0 ≠ w 1)
    (x y u v : Fin 6)
    (hx : x ≠ 4 ∧ x ≠ Fin.castAdd 2 (w 0) ∧ x ≠ Fin.castAdd 2 (w 1))
    (hy : y ≠ 4 ∧ y ≠ Fin.castAdd 2 (w 0) ∧ y ≠ Fin.castAdd 2 (w 1))
    (hu : u ≠ 4 ∧ u ≠ Fin.castAdd 2 (w 2) ∧ u ≠ Fin.castAdd 2 (w 1))
    (hv : v ≠ 4 ∧ v ≠ Fin.castAdd 2 (w 2) ∧ v ≠ Fin.castAdd 2 (w 1))
    (hxy : x ≠ y) (huv : u ≠ v)
    (hdis : x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v) : False := by
  have h12 : w 1 ≠ w 2 := by
    intro h
    have hh : (0 : Fin 4) = 1 := h27 (by simpa using h)
    exact (by decide : (0 : Fin 4) ≠ 1) hh
  have h16 : w 1 ≠ w 6 := by
    intro h
    have hh : (0 : Fin 4) = 2 := h27 (by simpa using h)
    exact (by decide : (0 : Fin 4) ≠ 2) hh
  have h17 : w 1 ≠ w 7 := by
    intro h
    have hh : (0 : Fin 4) = 3 := h27 (by simpa using h)
    exact (by decide : (0 : Fin 4) ≠ 3) hh
  have h26 : w 2 ≠ w 6 := by
    intro h
    have hh : (1 : Fin 4) = 2 := h27 (by simpa using h)
    exact (by decide : (1 : Fin 4) ≠ 2) hh
  have h27' : w 2 ≠ w 7 := by
    intro h
    have hh : (1 : Fin 4) = 3 := h27 (by simpa using h)
    exact (by decide : (1 : Fin 4) ≠ 3) hh
  have h67 : w 6 ≠ w 7 := by
    intro h
    have hh : (2 : Fin 4) = 3 := h27 (by simpa using h)
    exact (by decide : (2 : Fin 4) ≠ 3) hh
  have h06 : w 0 ≠ w 6 := by
    intro h
    have hh : (3 : Fin 4) = 1 := h60 (by simpa using h)
    exact (by decide : (3 : Fin 4) ≠ 1) hh
  have h07 : w 0 ≠ w 7 := by
    intro h
    have hh : (3 : Fin 4) = 2 := h60 (by simpa using h)
    exact (by decide : (3 : Fin 4) ≠ 2) hh
  have heq : w 0 = w 2 :=
    op874_contraction_forces_equal_factor_palette (w 1) (w 2) (w 6) (w 7) (w 0)
      h12 h16 h17 h26 h27' h67 hp h06 h07
  have hlow0 : (4 : Fin 6) ≠ Fin.castAdd 2 (w 0) := by
    intro h
    have hv := congrArg Fin.val h
    have hw := (w 0).isLt
    simp only [Fin.val_castAdd] at hv
    omega
  have hlow1 : (4 : Fin 6) ≠ Fin.castAdd 2 (w 1) := by
    intro h
    have hv := congrArg Fin.val h
    have hw := (w 1).isLt
    simp only [Fin.val_castAdd] at hv
    omega
  have hhigh : Fin.castAdd 2 (w 0) ≠ Fin.castAdd 2 (w 1) := by
    intro h
    apply hp
    apply Fin.ext
    simpa only [Fin.val_castAdd] using congrArg Fin.val h
  rw [← heq] at hu hv
  rcases equal_external_triple_forces_shared_exposed_color 4
      (Fin.castAdd 2 (w 0)) (Fin.castAdd 2 (w 1)) x y u v
      hlow0 hlow1 hhigh hx hy hu hv hxy huv with h | h | h | h
  · exact hdis.1 h
  · exact hdis.2.1 h
  · exact hdis.2.2.1 h
  · exact hdis.2.2.2 h
