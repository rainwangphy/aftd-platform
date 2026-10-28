import AFTD.Prelude

/-!
# is_tree_card_coloring_three_leaf

Topic: graphs   Node: 64f4899eed17

Provenance: helper lemma. step towards is_tree_card_coloring_three

Removing a leaf of degree 1 from a graph halves the number of proper 3-colorings (each coloring of T \ {v} extends in exactly 2 ways to v).
-/

/-- Removing a leaf of degree 1 from a graph halves the number of proper 3-colorings (each coloring of T \ {v} extends in exactly 2 ways to v). -/
lemma is_tree_card_coloring_three_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v : V} (hv : T.degree v = 1) :
    Fintype.card (T.Coloring (Fin 3)) = 2 * Fintype.card ((T.induce {v}ᶜ).Coloring (Fin 3)) := by
  classical
  obtain ⟨u, huv, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hv
  have humem : u ∈ ({v}ᶜ : Set V) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (SimpleGraph.ne_of_adj T huv).symm
  let restr : T.Coloring (Fin 3) → (T.induce {v}ᶜ).Coloring (Fin 3) :=
    fun C => SimpleGraph.Coloring.mk (fun (x : ↥({v}ᶜ : Set V)) => C x.val)
      (fun {x y} h => C.valid h)
  let Aty := {p : ((T.induce {v}ᶜ).Coloring (Fin 3)) × Fin 3 // p.2 ≠ p.1 ⟨u, humem⟩}
  let g : Aty → T.Coloring (Fin 3) :=
    fun p => SimpleGraph.Coloring.mk
      (fun w : V => if h : w ∈ ({v}ᶜ : Set V) then p.1.1 ⟨w, h⟩ else p.1.2)
      (fun {x y} hxy => by
        by_cases hxv : x = v
        · subst hxv
          have hyu : y = u := huniq y hxy
          subst hyu
          rw [dif_neg (by simp), dif_pos humem]
          exact p.2
        · by_cases hy : y ∈ ({v}ᶜ : Set V)
          · rw [dif_pos (by simpa using hxv), dif_pos hy]
            exact p.1.1.valid hxy
          · rw [dif_pos (by simpa using hxv), dif_neg hy]
            have hyv : y = v := by
              simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
              exact not_not.mp hy
            have hxu : x = u := by
              refine huniq x ?_
              rw [← hyv]
              exact hxy.symm
            intro hcontra
            refine p.2 ?_
            calc p.1.2 = p.1.1 ⟨x, by simpa using hxv⟩ := hcontra.symm
              _ = p.1.1 ⟨u, humem⟩ := by
                rw [show (⟨x, by simpa using hxv⟩ : ↥({v}ᶜ : Set V)) = ⟨u, humem⟩
                  from Subtype.ext hxu])
  let f : T.Coloring (Fin 3) → Aty := fun C => ⟨(restr C, C v), C.valid huv⟩
  have hleft : Function.LeftInverse g f := by
    intro C
    apply RelHom.ext
    intro w
    show (if h : w ∈ ({v}ᶜ : Set V) then (restr C) ⟨w, h⟩ else C v) = C w
    by_cases hw : w ∈ ({v}ᶜ : Set V)
    · rw [dif_pos hw]
      rfl
    · rw [dif_neg hw]
      have hwv : w = v := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        exact not_not.mp hw
      rw [hwv]
  have hright : Function.RightInverse g f := by
    intro p
    have h1 : restr (g p) = p.1.1 := by
      apply RelHom.ext
      intro w
      show (if h : w.1 ∈ ({v}ᶜ : Set V) then p.1.1 ⟨w.1, h⟩ else p.1.2) = p.1.1 w
      rw [dif_pos w.2]
    have h2 : (g p) v = p.1.2 := by
      show (if h : v ∈ ({v}ᶜ : Set V) then p.1.1 ⟨v, h⟩ else p.1.2) = p.1.2
      rw [dif_neg (by simp)]
    exact Subtype.ext (Prod.ext h1 h2)
  have e1 : T.Coloring (Fin 3) ≃ Aty :=
    Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩
  have e2 : Aty ≃
      (Σ r : (T.induce {v}ᶜ).Coloring (Fin 3), {a : Fin 3 // a ≠ r ⟨u, humem⟩}) :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun s => ⟨(s.1, s.2.val), s.2.property⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  have h2c : ∀ x : Fin 3, Fintype.card {a : Fin 3 // a ≠ x} = 2 := by
    intro x
    fin_cases x <;> decide
  rw [Fintype.card_congr e1, Fintype.card_congr e2, Fintype.card_sigma]
  simp only [h2c, Finset.sum_const, Finset.card_univ]
  show Fintype.card ((T.induce {v}ᶜ).Coloring (Fin 3)) * 2 =
    2 * Fintype.card ((T.induce {v}ᶜ).Coloring (Fin 3))
  exact Nat.mul_comm _ _
