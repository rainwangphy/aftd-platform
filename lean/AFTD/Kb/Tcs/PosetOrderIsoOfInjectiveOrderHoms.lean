import AFTD.Prelude

/-!
# poset_order_iso_of_injective_order_homs

Topic: combinatorics   Node: 8b0959770ce1

Provenance: helper lemma. step towards poset_nonempty_order_iso_of_card_order_hom_eq_of_connected

Two finite posets with mutual injective order homomorphisms are order-isomorphic. The permutation g ∘ f on X has finite order k, so its inverse (g ∘ f)^{k-1} is order-preserving; hence f^{-1} = (g ∘ f)^{-1} ∘ g is order-preserving.
-/

/-- Two finite posets with mutual injective order homomorphisms are order-isomorphic (finite poset Cantor-Bernstein theorem). -/
theorem poset_order_iso_of_injective_order_homs {X Y : Type*} [Fintype X] [Fintype Y]
    [PartialOrder X] [PartialOrder Y]
    (f : X →o Y) (g : Y →o X) (hf : Function.Injective f) (hg : Function.Injective g) :
    Nonempty (X ≃o Y) := by
  have hcard : Fintype.card X = Fintype.card Y := by
    apply le_antisymm
    · exact Fintype.card_le_of_injective f hf
    · exact Fintype.card_le_of_injective g hg
  have hfb : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, hcard⟩
  let ef : X ≃ Y := Equiv.ofBijective f hfb
  let e : X → X := fun x => g (f x)
  have he_inj : Function.Injective e := by
    exact hg.comp hf
  have he_bij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he_inj, rfl⟩
  let p : Equiv.Perm X := Equiv.ofBijective e he_bij
  have hp_e : (⇑p) = e := by
    ext x
    simp [p, e]
  have hp_mono : Monotone e := by
    exact g.monotone.comp f.monotone
  let n : ℕ := orderOf p
  have hn_pos : 0 < n := by
    dsimp [n]
    exact orderOf_pos p
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn_pos
  have hp_pred : p ^ (n - 1) * p = 1 := by
    calc
      p ^ (n - 1) * p = p ^ ((n - 1) + 1) := (pow_succ p (n - 1)).symm
      _ = p ^ n := by rw [Nat.sub_add_cancel hn1]
      _ = 1 := pow_orderOf_eq_one p
  have hp_left_inv : ∀ x, (p ^ (n - 1)) (p x) = x := by
    intro x
    have := congrFun (congrArg (fun q : Equiv.Perm X => (q : X → X)) hp_pred) x
    simpa [Equiv.Perm.mul_apply] using this
  have hp_pred_mono : Monotone (fun x => (p ^ (n - 1)) x) := by
    rw [show (fun x => (p ^ (n - 1)) x) = e^[n - 1] by
      funext x
      rw [Equiv.Perm.coe_pow]
      simp [hp_e]]
    exact hp_mono.iterate (n - 1)
  have hreflect : ∀ a b, f a ≤ f b → a ≤ b := by
    intro a b hab
    have h1 : e a ≤ e b := g.monotone hab
    have h1' : p a ≤ p b := by simpa [hp_e] using h1
    have h2 : (p ^ (n - 1)) (p a) ≤ (p ^ (n - 1)) (p b) := hp_pred_mono h1'
    simpa [hp_left_inv] using h2
  refine ⟨RelIso.mk ef ?_⟩
  intro a b
  constructor
  · intro h
    apply hreflect a b
    simpa [ef] using h
  · intro h
    simpa [ef] using f.monotone h
