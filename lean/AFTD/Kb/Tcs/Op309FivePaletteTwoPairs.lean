import AFTD.Prelude

/-!
# op309_five_palette_two_pairs

Topic: graphs   Node: 119659de290d

Provenance: helper lemma. OP-309 local P3 port pairing obstruction; experiments 41711-41716.

Two injective five-color lists with three shared entries have the same remaining pair up to swapping.
-/

theorem op309_five_palette_two_pairs
    (p q r a b x y : Fin 5)
    (hfirst : ([p,q,r,a,b] : List (Fin 5)).Nodup)
    (hsecond : ([p,q,r,x,y] : List (Fin 5)).Nodup) :
    (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
  set_option maxHeartbeats 4000000 in
    classical
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at hfirst hsecond
    let f : Fin 5 → Fin 5 := ![p,q,r,a,b]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have cover (z : Fin 5) : z=p ∨ z=q ∨ z=r ∨ z=a ∨ z=b := by
      obtain ⟨i,hi⟩ := (Finite.surjective_of_injective hf) z
      fin_cases i <;> simp_all [f]
    rcases cover x with h | h | h | h | h <;> simp_all
    all_goals rcases cover y with h | h | h | h | h <;> simp_all
