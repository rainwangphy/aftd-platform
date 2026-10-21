import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphBindingNumber
import AFTD.Kb.Tcs.SimpleGraphBindingNumberLeIff

/-!
# simple_graph_binding_number_complete

Topic: graphs   Node: 0cecbff3f5ff

Provenance: helper lemma. sanity lemma for simple_graph_binding_number; serves OP-422

The complete graph K_n (n ≥ 2) has binding number n − 1: a singleton {v} has N = V∖{v}, and any S with two vertices has N(S) = V.
-/

theorem simple_graph_binding_number_complete (n : ℕ) (hn : 2 ≤ n) :
    simple_graph_binding_number (⊤ : SimpleGraph (Fin n)) = (n : ℝ) - 1 := by
  refine le_antisymm ?_ ?_
  · have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [simple_graph_binding_number_le_iff]
    let v : Fin n := ⟨0, by omega⟩
    refine ⟨{v}, Finset.singleton_nonempty v, ?_, ?_⟩
    · simp only [Finset.singleton_biUnion]
      intro h
      have : v ∉ (⊤ : SimpleGraph (Fin n)).neighborFinset v := by simp
      rw [h] at this
      exact this (Finset.mem_univ v)
    · simp only [Finset.singleton_biUnion, Finset.card_singleton, Nat.cast_one, mul_one]
      have hnv : (⊤ : SimpleGraph (Fin n)).neighborFinset v = Finset.univ.erase v := by
        ext x; simp
      rw [hnv, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
      have : 1 ≤ n := by omega
      exact le_of_eq (Nat.cast_pred this)
  · let v : Fin n := ⟨0, by omega⟩
    have hne_univ : ({v} : Finset (Fin n)).biUnion (fun u => (⊤ : SimpleGraph (Fin n)).neighborFinset u) ≠ Finset.univ := by
      simp only [Finset.singleton_biUnion]
      intro h
      have : v ∉ (⊤ : SimpleGraph (Fin n)).neighborFinset v := by simp
      rw [h] at this
      exact this (Finset.mem_univ v)
    have : Nonempty { S : Finset (Fin n) // S.Nonempty ∧ S.biUnion (fun u => (⊤ : SimpleGraph (Fin n)).neighborFinset u) ≠ Finset.univ } :=
      ⟨⟨{v}, Finset.singleton_nonempty v, hne_univ⟩⟩
    dsimp [simple_graph_binding_number]
    apply le_ciInf
    rintro ⟨S, hSne, hSuniv⟩
    change (n : ℝ) - 1 ≤ ((S.biUnion (fun u => (⊤ : SimpleGraph (Fin n)).neighborFinset u)).card : ℝ) / (S.card : ℝ)
    have hall_eq : ∀ u ∈ S, ∀ w ∈ S, u = w := by
      intro u hu w hw
      by_contra hne
      have huniv : S.biUnion (fun x => (⊤ : SimpleGraph (Fin n)).neighborFinset x) = Finset.univ := by
        ext x
        simp only [Finset.mem_biUnion, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj, Finset.mem_univ, iff_true]
        by_cases hxu : x = u
        · refine ⟨w, hw, ?_⟩
          rw [hxu]
          exact Ne.symm hne
        · refine ⟨u, hu, Ne.symm hxu⟩
      exact hSuniv huniv
    obtain ⟨u, hu⟩ := hSne
    have hS_eq : S = {u} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx; exact hall_eq x hx u hu
      · rintro rfl; exact hu
    rw [hS_eq]
    simp only [Finset.singleton_biUnion, Finset.card_singleton, Nat.cast_one, div_one]
    have hnv : (⊤ : SimpleGraph (Fin n)).neighborFinset u = Finset.univ.erase u := by
      ext x; simp
    rw [hnv, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := by omega
    exact le_of_eq (Nat.cast_pred this).symm
