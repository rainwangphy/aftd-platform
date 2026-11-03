import AFTD.Prelude

/-!
# truncation_local_state_internal_cover

Topic: graphs   Node: 96def392dce9

Provenance: helper lemma. helper for truncation_local_states_strong_coloring_iff (arXiv:2610.41950 Lemma 2.1, PR-677)

With six colours, a local state at v (c v injective on the three edges at v, h v injective there, and no h v e equal to any c v f) has h v mapping onto I_v: every colour ω different from all c v f (f at v) equals h v g for some edge g at v.
-/

theorem truncation_local_state_internal_cover {V E Ω : Type*} [Fintype Ω]
    (hΩ : Fintype.card Ω = 6) {ends : E → Sym2 V}
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3) {c h : V → E → Ω}
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    {v : V} {ω : Ω} (hω : ∀ f, v ∈ ends f → c v f ≠ ω) : ∃ g, v ∈ ends g ∧ h v g = ω := by
  by_contra hno
  push Not at hno
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp (hcubic v)
  have mem : ∀ k, v ∈ ends k ↔ k = x ∨ k = y ∨ k = z := fun k => by
    have := Set.ext_iff.mp hs k
    simpa using this
  have hx := (mem x).2 (Or.inl rfl)
  have hy := (mem y).2 (Or.inr (Or.inl rfl))
  have hz := (mem z).2 (Or.inr (Or.inr rfl))
  have a1 := hω x hx
  have a2 := hω y hy
  have a3 := hω z hz
  have b1 := hno x hx
  have b2 := hno y hy
  have b3 := hno z hz
  have c1 : c v x ≠ c v y := fun e => hxy (hc v x y hx hy e)
  have c2 : c v x ≠ c v z := fun e => hxz (hc v x z hx hz e)
  have c3 : c v y ≠ c v z := fun e => hyz (hc v y z hy hz e)
  have d1 : h v x ≠ h v y := fun e => hxy (hh v x y hx hy e)
  have d2 : h v x ≠ h v z := fun e => hxz (hh v x z hx hz e)
  have d3 : h v y ≠ h v z := fun e => hyz (hh v y z hy hz e)
  have e1 := hch v x x hx hx
  have e2 := hch v x y hx hy
  have e3 := hch v x z hx hz
  have e4 := hch v y x hy hx
  have e5 := hch v y y hy hy
  have e6 := hch v y z hy hz
  have e7 := hch v z x hz hx
  have e8 := hch v z y hz hy
  have e9 := hch v z z hz hz
  let F : Fin 7 → Ω := ![ω, c v x, c v y, c v z, h v x, h v y, h v z]
  have hF : Function.Injective F := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (simp [F] at hij <;> first
          | exact absurd hij (by assumption)
          | exact absurd hij.symm (by assumption))
  have := Fintype.card_le_of_injective F hF
  rw [Fintype.card_fin, hΩ] at this
  omega
