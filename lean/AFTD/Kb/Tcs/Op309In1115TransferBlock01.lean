import AFTD.Prelude

/-!
# op309_in1115_transfer_block_01

Topic: graphs   Node: 993fa5e94df7

Provenance: helper lemma. OP-309 triangle expansion repair obstruction

Block 2 of the finite graph-to-propositional transfer for the triangle expansion counterexample.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option linter.unusedVariables false

private def in1115_adj {n m : ℕ} (E : Fin n → Fin m × Fin m) (i j : Fin n) : Prop :=
 i ≠ j ∧ ((E i).1 = (E j).1 ∨ (E i).1 = (E j).2 ∨ (E i).2 = (E j).1 ∨ (E i).2 = (E j).2)
private def in1115_rich {n m : ℕ} (E : Fin n → Fin m × Fin m) (D : Fin n → Fin 5) (i : Fin n) : Prop :=
 ∀ j k, in1115_adj E i j → in1115_adj E i k → j ≠ k → D j ≠ D k
private def in1115_good {n m : ℕ} (E : Fin n → Fin m × Fin m) (D : Fin n → Fin 5) : Prop :=
 (∀ i j, in1115_adj E i j → D i ≠ D j) ∧ ∀ i, (∃ j, in1115_adj E i j) → ∃ j, in1115_adj E i j ∧ in1115_rich E D j

private def in1115_graph : Fin 39 → Fin 26 × Fin 26 := ![(0,1),(24,2),(25,3),(9,4),(9,14),(9,19),(12,6),(12,7),(12,20),(13,5),(13,1),(13,22),(4,15),(4,17),(5,20),(5,21),(6,10),(6,23),(7,11),(7,16),(8,15),(8,16),(8,21),(1,23),(10,3),(10,20),(11,2),(11,16),(2,18),(3,14),(14,22),(15,18),(17,19),(17,22),(18,19),(21,23),(0,24),(24,25),(25,0)]
private def in1115_colors : Fin 36 → Fin 5 := ![0,1,2,2,3,4,0,2,3,2,3,4,1,0,4,0,4,1,1,4,3,0,1,4,3,1,4,3,3,4,2,4,3,1,2,3]
private def in1115_bad (D : Fin 39 → Fin 5) (i : Fin 33) : Prop := D ⟨i.val+3, by omega⟩ ≠ in1115_colors ⟨i.val+3, by omega⟩
local instance  aftdLocal_1440c7d3e38e0223_0 (D : Fin 39 → Fin 5) : DecidablePred (in1115_bad D) := by
  intro i; unfold in1115_bad; infer_instance
local instance  aftdLocal_1440c7d3e38e0223_1 {n m : ℕ} (E : Fin n → Fin m × Fin m) (i j : Fin n) : Decidable (in1115_adj E i j) := by
  unfold in1115_adj; infer_instance
private def in1115_one (D : Fin 39 → Fin 5) (t : ℕ) : Prop := ∃ i : Fin 33, i.val ≤ t ∧ in1115_bad D i
private def in1115_two (D : Fin 39 → Fin 5) (t : ℕ) : Prop := ∃ i j : Fin 33, i.val < j.val ∧ j.val ≤ t ∧ in1115_bad D i ∧ in1115_bad D j


private theorem in1115_local_prefix {n : ℕ} (bad : Fin n → Prop) [DecidablePred bad]
    (hcard : (Finset.univ.filter bad).card ≤ 2) :
    let one : ℕ → Prop := fun t => ∃ i : Fin n, i.val ≤ t ∧ bad i
    let two : ℕ → Prop := fun t => ∃ i j : Fin n, i.val < j.val ∧ j.val ≤ t ∧ bad i ∧ bad j
    (∀ i : Fin n, bad i → one i.val) ∧
    (∀ t, one t → one (t+1)) ∧
    (∀ i : Fin n, bad i → i.val > 0 → one (i.val-1) → two i.val) ∧
    (∀ t, two t → two (t+1)) ∧
    (∀ i : Fin n, bad i → i.val > 0 → ¬ two (i.val-1)) ∧
    ¬ two 0 := by
  dsimp only
  have no_three (i j k : Fin n) (hij : i.val < j.val) (hjk : j.val < k.val)
      (hi : bad i) (hj : bad j) (hk : bad k) : False := by
    have hij' : i ≠ j := by intro h; subst j; omega
    have hik' : i ≠ k := by intro h; subst k; omega
    have hjk' : j ≠ k := by intro h; subst k; omega
    have hs : ({i,j,k} : Finset (Fin n)) ⊆ Finset.univ.filter bad := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hs
    simp [hij', hik', hjk'] at hc
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact ⟨i, le_rfl, hi⟩
  · intro t ⟨i,hi,hb⟩; exact ⟨i, by omega, hb⟩
  · intro i hi hpos ⟨j,hj,hb⟩; exact ⟨j,i,by omega,le_rfl,hb,hi⟩
  · intro t ⟨i,j,hij,hj,hi,hb⟩; exact ⟨i,j,hij,by omega,hi,hb⟩
  · intro i hi hpos ⟨j,k,hjk,hk,hj,hkb⟩
    exact no_three j k i hjk (by omega) hj hkb hi
  · rintro ⟨i,j,hij,hj,_,_⟩
    omega

theorem op309_in1115_transfer_block_01 (D : Fin 39 → Fin 5) (hg : in1115_good in1115_graph D)
    (hcard : (Finset.univ.filter (in1115_bad D)).card ≤ 2) (h : (((((((((D 20 = 3) ∧ (D 20 = 4)) ∨ ((D 21 = 0) ∧ (D 21 = 1))) ∨ (((D 21 = 0) ∧ (D 21 = 2)) ∨ ((D 21 = 0) ∧ (D 21 = 3)))) ∨ ((((D 21 = 0) ∧ (D 21 = 4)) ∨ ((D 22 = 0) ∧ (D 22 = 1))) ∨ (((D 22 = 1) ∧ (D 22 = 2)) ∨ ((D 22 = 1) ∧ (D 22 = 3))))) ∨ (((((D 22 = 1) ∧ (D 22 = 4)) ∨ (¬ (D 23 = 0) ∧ (¬ (D 23 = 1) ∧ (¬ (D 23 = 2) ∧ (¬ (D 23 = 3) ∧ ¬ (D 23 = 4)))))) ∨ (((D 23 = 0) ∧ (D 23 = 4)) ∨ ((D 23 = 1) ∧ (D 23 = 4)))) ∨ ((((D 23 = 2) ∧ (D 23 = 4)) ∨ ((D 23 = 3) ∧ (D 23 = 4))) ∨ ((¬ (D 24 = 0) ∧ (¬ (D 24 = 1) ∧ (¬ (D 24 = 2) ∧ (¬ (D 24 = 3) ∧ ¬ (D 24 = 4))))) ∨ ((D 24 = 0) ∧ (D 24 = 1)))))) ∨ ((((((D 24 = 0) ∧ (D 24 = 2)) ∨ ((D 24 = 0) ∧ (D 24 = 3))) ∨ (((D 24 = 0) ∧ (D 24 = 4)) ∨ ((D 24 = 1) ∧ (D 24 = 2)))) ∨ ((((D 24 = 1) ∧ (D 24 = 3)) ∨ ((D 24 = 2) ∧ (D 24 = 3))) ∨ (((D 24 = 2) ∧ (D 24 = 4)) ∨ ((D 24 = 3) ∧ (D 24 = 4))))) ∨ ((((¬ (D 25 = 0) ∧ (¬ (D 25 = 1) ∧ (¬ (D 25 = 2) ∧ (¬ (D 25 = 3) ∧ ¬ (D 25 = 4))))) ∨ ((D 25 = 0) ∧ (D 25 = 1))) ∨ (((D 25 = 1) ∧ (D 25 = 2)) ∨ ((D 25 = 1) ∧ (D 25 = 3)))) ∨ ((((D 25 = 1) ∧ (D 25 = 4)) ∨ (¬ (D 26 = 0) ∧ (¬ (D 26 = 1) ∧ (¬ (D 26 = 2) ∧ (¬ (D 26 = 3) ∧ ¬ (D 26 = 4)))))) ∨ (((D 26 = 0) ∧ (D 26 = 4)) ∨ ((D 26 = 1) ∧ (D 26 = 4))))))) ∨ (((((((D 26 = 2) ∧ (D 26 = 4)) ∨ ((D 26 = 3) ∧ (D 26 = 4))) ∨ ((¬ (D 27 = 0) ∧ (¬ (D 27 = 1) ∧ (¬ (D 27 = 2) ∧ (¬ (D 27 = 3) ∧ ¬ (D 27 = 4))))) ∨ ((D 27 = 0) ∧ (D 27 = 3)))) ∨ ((((D 27 = 1) ∧ (D 27 = 3)) ∨ ((D 27 = 2) ∧ (D 27 = 3))) ∨ (((D 27 = 3) ∧ (D 27 = 4)) ∨ (¬ (D 28 = 0) ∧ (¬ (D 28 = 1) ∧ (¬ (D 28 = 2) ∧ (¬ (D 28 = 3) ∧ ¬ (D 28 = 4)))))))) ∨ (((((D 28 = 0) ∧ (D 28 = 3)) ∨ ((D 28 = 1) ∧ (D 28 = 3))) ∨ (((D 28 = 2) ∧ (D 28 = 3)) ∨ ((D 28 = 3) ∧ (D 28 = 4)))) ∨ (((¬ (D 29 = 0) ∧ (¬ (D 29 = 1) ∧ (¬ (D 29 = 2) ∧ (¬ (D 29 = 3) ∧ ¬ (D 29 = 4))))) ∨ ((D 29 = 0) ∧ (D 29 = 1))) ∨ (((D 29 = 0) ∧ (D 29 = 4)) ∨ ((D 29 = 1) ∧ (D 29 = 2)))))) ∨ ((((((D 29 = 1) ∧ (D 29 = 3)) ∨ ((D 29 = 1) ∧ (D 29 = 4))) ∨ (((D 29 = 2) ∧ (D 29 = 4)) ∨ ((D 29 = 3) ∧ (D 29 = 4)))) ∨ (((¬ (D 30 = 0) ∧ (¬ (D 30 = 1) ∧ (¬ (D 30 = 2) ∧ (¬ (D 30 = 3) ∧ ¬ (D 30 = 4))))) ∨ ((D 30 = 0) ∧ (D 30 = 1))) ∨ (((D 30 = 0) ∧ (D 30 = 2)) ∨ ((D 30 = 1) ∧ (D 30 = 2))))) ∨ (((((D 30 = 2) ∧ (D 30 = 3)) ∨ ((D 30 = 2) ∧ (D 30 = 4))) ∨ ((¬ (D 31 = 0) ∧ (¬ (D 31 = 1) ∧ (¬ (D 31 = 2) ∧ (¬ (D 31 = 3) ∧ ¬ (D 31 = 4))))) ∨ ((D 31 = 0) ∧ (D 31 = 4)))) ∨ ((((D 31 = 1) ∧ (D 31 = 4)) ∨ ((D 31 = 2) ∧ (D 31 = 4))) ∨ (((D 31 = 3) ∧ (D 31 = 4)) ∨ (((D 32 = 0) ∧ (D 32 = 3)) ∨ ((D 32 = 1) ∧ (D 32 = 3))))))))) ∨ ((((((((D 32 = 2) ∧ (D 32 = 3)) ∨ ((D 32 = 3) ∧ (D 32 = 4))) ∨ ((¬ (D 33 = 0) ∧ (¬ (D 33 = 1) ∧ (¬ (D 33 = 2) ∧ (¬ (D 33 = 3) ∧ ¬ (D 33 = 4))))) ∨ ((D 33 = 0) ∧ (D 33 = 1)))) ∨ ((((D 33 = 1) ∧ (D 33 = 2)) ∨ ((D 33 = 1) ∧ (D 33 = 3))) ∨ (((D 33 = 1) ∧ (D 33 = 4)) ∨ (¬ (D 34 = 0) ∧ (¬ (D 34 = 1) ∧ (¬ (D 34 = 2) ∧ (¬ (D 34 = 3) ∧ ¬ (D 34 = 4)))))))) ∨ (((((D 34 = 0) ∧ (D 34 = 2)) ∨ ((D 34 = 1) ∧ (D 34 = 2))) ∨ (((D 34 = 2) ∧ (D 34 = 3)) ∨ ((D 34 = 2) ∧ (D 34 = 4)))) ∨ (((¬ (D 35 = 0) ∧ (¬ (D 35 = 1) ∧ (¬ (D 35 = 2) ∧ (¬ (D 35 = 3) ∧ ¬ (D 35 = 4))))) ∨ ((D 35 = 0) ∧ (D 35 = 3))) ∨ (((D 35 = 1) ∧ (D 35 = 3)) ∨ ((D 35 = 2) ∧ (D 35 = 3)))))) ∨ ((((((D 35 = 3) ∧ (D 35 = 4)) ∨ (¬ (D 36 = 0) ∧ (¬ (D 36 = 1) ∧ (¬ (D 36 = 2) ∧ (¬ (D 36 = 3) ∧ ¬ (D 36 = 4)))))) ∨ (((D 36 = 0) ∧ (D 36 = 1)) ∨ ((D 36 = 0) ∧ (D 36 = 2)))) ∨ ((((D 36 = 0) ∧ (D 36 = 3)) ∨ ((D 36 = 0) ∧ (D 36 = 4))) ∨ (((D 36 = 1) ∧ (D 36 = 2)) ∨ ((D 36 = 1) ∧ (D 36 = 3))))) ∨ (((((D 36 = 1) ∧ (D 36 = 4)) ∨ ((D 36 = 2) ∧ (D 36 = 3))) ∨ (((D 36 = 2) ∧ (D 36 = 4)) ∨ ((D 36 = 3) ∧ (D 36 = 4)))) ∨ (((¬ (D 37 = 0) ∧ (¬ (D 37 = 1) ∧ (¬ (D 37 = 2) ∧ (¬ (D 37 = 3) ∧ ¬ (D 37 = 4))))) ∨ ((D 37 = 0) ∧ (D 37 = 1))) ∨ (((D 37 = 0) ∧ (D 37 = 2)) ∨ (((D 37 = 0) ∧ (D 37 = 3)) ∨ ((D 37 = 0) ∧ (D 37 = 4)))))))) ∨ (((((((D 37 = 1) ∧ (D 37 = 2)) ∨ ((D 37 = 1) ∧ (D 37 = 3))) ∨ (((D 37 = 1) ∧ (D 37 = 4)) ∨ ((D 37 = 2) ∧ (D 37 = 3)))) ∨ ((((D 37 = 2) ∧ (D 37 = 4)) ∨ ((D 37 = 3) ∧ (D 37 = 4))) ∨ ((¬ (D 38 = 0) ∧ (¬ (D 38 = 1) ∧ (¬ (D 38 = 2) ∧ (¬ (D 38 = 3) ∧ ¬ (D 38 = 4))))) ∨ ((D 38 = 0) ∧ (D 38 = 1))))) ∨ (((((D 38 = 0) ∧ (D 38 = 2)) ∨ ((D 38 = 0) ∧ (D 38 = 3))) ∨ (((D 38 = 0) ∧ (D 38 = 4)) ∨ ((D 38 = 1) ∧ (D 38 = 2)))) ∨ ((((D 38 = 1) ∧ (D 38 = 3)) ∨ ((D 38 = 1) ∧ (D 38 = 4))) ∨ (((D 38 = 2) ∧ (D 38 = 3)) ∨ ((D 38 = 2) ∧ (D 38 = 4)))))) ∨ ((((((D 38 = 3) ∧ (D 38 = 4)) ∨ ((D 0 = 0) ∧ (D 10 = 0))) ∨ (((D 0 = 1) ∧ (D 10 = 1)) ∨ ((D 0 = 2) ∧ (D 10 = 2)))) ∨ ((((D 0 = 3) ∧ (D 10 = 3)) ∨ ((D 0 = 4) ∧ (D 10 = 4))) ∨ (((D 0 = 0) ∧ (D 23 = 0)) ∨ ((D 0 = 1) ∧ (D 23 = 1))))) ∨ (((((D 0 = 2) ∧ (D 23 = 2)) ∨ ((D 0 = 3) ∧ (D 23 = 3))) ∨ (((D 0 = 4) ∧ (D 23 = 4)) ∨ ((D 0 = 0) ∧ (D 36 = 0)))) ∨ ((((D 0 = 1) ∧ (D 36 = 1)) ∨ ((D 0 = 2) ∧ (D 36 = 2))) ∨ (((D 0 = 3) ∧ (D 36 = 3)) ∨ (((D 0 = 4) ∧ (D 36 = 4)) ∨ ((D 0 = 0) ∧ (D 38 = 0))))))))))) : False := by
  have hc := in1115_local_prefix (in1115_bad D) hcard
  change (∀ i : Fin 33, in1115_bad D i → in1115_one D i.val) ∧
    (∀ t, in1115_one D t → in1115_one D (t+1)) ∧
    (∀ i : Fin 33, in1115_bad D i → i.val > 0 → in1115_one D (i.val-1) → in1115_two D i.val) ∧
    (∀ t, in1115_two D t → in1115_two D (t+1)) ∧
    (∀ i : Fin 33, in1115_bad D i → i.val > 0 → ¬ in1115_two D (i.val-1)) ∧
    ¬ in1115_two D 0 at hc
  rcases h with h | h
  ·
    rcases h with h | h
    ·
      rcases h with h | h
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 23 = v
                fin_cases v <;> simp_all
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 24 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 25 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 26 = v
                fin_cases v <;> simp_all
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
    ·
      rcases h with h | h
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 27 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 28 = v
                fin_cases v <;> simp_all
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 29 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 30 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 31 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with h | h
                ·
                  rcases h with ⟨h0,h1⟩
                  omega
                ·
                  rcases h with ⟨h0,h1⟩
                  omega
  ·
    rcases h with h | h
    ·
      rcases h with h | h
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 33 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 34 = v
                fin_cases v <;> simp_all
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 35 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 36 = v
                fin_cases v <;> simp_all
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 37 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with h | h
                ·
                  rcases h with ⟨h0,h1⟩
                  omega
                ·
                  rcases h with ⟨h0,h1⟩
                  omega
    ·
      rcases h with h | h
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1,h2,h3,h4⟩
                generalize hD : D 38 = v
                fin_cases v <;> simp_all
              ·
                rcases h with ⟨h0,h1⟩
                omega
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                omega
      ·
        rcases h with h | h
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                omega
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 10 (by decide)) (h0.trans h1.symm)
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 10 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 10 (by decide)) (h0.trans h1.symm)
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 10 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 10 (by decide)) (h0.trans h1.symm)
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 23 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 23 (by decide)) (h0.trans h1.symm)
        ·
          rcases h with h | h
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 23 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 23 (by decide)) (h0.trans h1.symm)
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 23 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 36 (by decide)) (h0.trans h1.symm)
          ·
            rcases h with h | h
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 36 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 36 (by decide)) (h0.trans h1.symm)
            ·
              rcases h with h | h
              ·
                rcases h with ⟨h0,h1⟩
                exact (hg.1 0 36 (by decide)) (h0.trans h1.symm)
              ·
                rcases h with h | h
                ·
                  rcases h with ⟨h0,h1⟩
                  exact (hg.1 0 36 (by decide)) (h0.trans h1.symm)
                ·
                  rcases h with ⟨h0,h1⟩
                  exact (hg.1 0 38 (by decide)) (h0.trans h1.symm)
