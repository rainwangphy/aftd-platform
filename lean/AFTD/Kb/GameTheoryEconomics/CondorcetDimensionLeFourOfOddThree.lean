import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_dimension_le_four_of_odd_three

Topic: social_choice   Node: 4180651ed53a

Provenance: helper lemma. IN-341 supporting reduction for the weaker universal-four target in OP-19. The remove-one-voter/add-that-voter-top-candidate argument is already in the proof of Proposition4 of Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . This helper is not new research.

If every finite strict-ranking election with a positive odd number of voters has a strict Condorcet winning set of size at most three, then every finite strict-ranking election with a positive number of voters has one of size at most four. This is a conditional reduction, not a proof of either universal existence premise.
-/

open Finset
open scoped BigOperators

theorem condorcet_dimension_le_four_of_odd_three
    (hodd : ∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)),
      0 < n → Odd n → ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S) :
    ∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
      ∃ S : Finset (Fin m), S.card ≤ 4 ∧ is_condorcet_winning_set P S := by
  intro n m P hn
  by_cases hodd_n : Odd n
  · obtain ⟨S, hSc, hSw⟩ := hodd n m P hn hodd_n
    exact ⟨S, by omega, hSw⟩
  · cases n with
    | zero => omega
    | succ k =>
      cases m with
      | zero =>
        refine ⟨∅, by simp, fun a _ => isEmptyElim a⟩
      | succ m' =>
        have heven : Even (k + 1) := Nat.not_odd_iff_even.mp hodd_n
        have hk_pos : 0 < k := by
          rcases heven with ⟨r, hr⟩
          cases r with
          | zero => omega
          | succ r => omega
        have hk_odd : Odd k := by
          rcases heven with ⟨r, hr⟩
          cases r with
          | zero => omega
          | succ r =>
            refine ⟨r, by omega⟩
        let P_prefix : Fin k → Equiv.Perm (Fin (m' + 1)) := fun i => P (Fin.castSucc i)
        obtain ⟨S, hSc, hSw⟩ := hodd k (m' + 1) P_prefix hk_pos hk_odd
        let c : Fin (m' + 1) := (P (Fin.last k)).symm 0
        refine ⟨insert c S, by have := Finset.card_insert_le c S; omega, ?_⟩
        intro a ha
        have ha_S : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
        have hSw_a := hSw a ha_S
        let p : Fin (k + 1) → Prop := fun v => ∀ b ∈ insert c S, P v a < P v b
        let q : Fin k → Prop := fun i => ∀ b ∈ S, P_prefix i a < P_prefix i b
        have hp_last : ¬ p (Fin.last k) := by
          intro h
          have hlt := h c (Finset.mem_insert_self c S)
          dsimp [c] at hlt
          rw [Equiv.apply_symm_apply] at hlt
          have : (P (Fin.last k) a).val < 0 := hlt
          omega
        obtain ⟨h1, h2⟩ : ∃ (h : Fin.last k ∉ Finset.univ.map Fin.castSuccEmb),
            (Finset.univ : Finset (Fin (k + 1))) = Finset.cons (Fin.last k) (Finset.univ.map Fin.castSuccEmb) h :=
          ⟨by simp [Finset.map_eq_image], Fin.univ_castSuccEmb k⟩
        have hp_eq : (Finset.univ.filter p).card = (Finset.univ.filter (fun i : Fin k => p (Fin.castSucc i))).card := by
          rw [h2, Finset.filter_cons_of_neg p (Fin.last k) (Finset.univ.map Fin.castSuccEmb) h1 hp_last,
              Finset.filter_map, Finset.card_map]
          rfl
        have h_sub : (Finset.univ.filter (fun i : Fin k => p (Fin.castSucc i))).card ≤ (Finset.univ.filter q).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro b hb
          exact hi b (Finset.mem_insert_of_mem hb)
        change 2 * (Finset.univ.filter p).card < k + 1
        have : (Finset.univ.filter q).card = (Finset.univ.filter (fun v => ∀ b ∈ S, P_prefix v a < P_prefix v b)).card := rfl
        omega
