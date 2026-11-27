import AFTD.Prelude

/-!
# op874_sixvertex_open_equal_cut_score

Topic: graphs   Node: 80cfd9105e37

Provenance: helper lemma. Six-vertex equal-port signature obstruction for OP-874; experiments 42699, 42701 and 42703.

For equal false port bits, the opened six-vertex example has matching-cut score at most four, attained exactly when the factor cycle is mixed.
-/

theorem op874_sixvertex_open_equal_cut_score (s t : Bool) :
  let L : Fin 10 → Fin 8 := ![0,0,0,1,1,1,2,2,2,3]
  let R : Fin 10 → Fin 8 := ![3,4,6,3,4,5,4,5,7,5]
  let ends : Fin 10 → Sym2 (Fin 8) := fun e => s(L e,R e)
  let M : Finset (Fin 10) := {2,4,8,9}
  let bit : Fin 8 → Bool := ![false,s,false,t,s,t,false,false]
  let cut : ℕ := ((Finset.univ : Finset (Fin 10)).filter fun e =>
    e ∉ M ∧ bit (L e) ≠ bit (R e)).card
  cut ≤ 4 ∧ (cut = 4 ↔ s = true ∨ t = true) := by
  cases s <;> cases t <;> decide
