import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEvalEqOfAgree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval
import AFTD.Kb.Tcs.MatroidIndepQueryTree

/-!
# matroid_connectedness_query_not_le_of_sensitive

Topic: algorithms   Node: 17d59d91fe77

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

Sensitivity lower bound. Let M be a connected matroid with ground set Fin n and F a family of finite subsets of Fin n such that for every S in F there is a disconnected matroid N with ground set Fin n whose independent sets agree with those of M on every finite set other than S. Then deciding connectedness on n elements needs at least |F| independence queries: matroid_connectedness_query_le n q fails for every q < |F|.
-/

theorem matroid_connectedness_query_not_le_of_sensitive {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (hM : matroid_connected M) (F : Finset (Finset (Fin n)))
    (hF : ∀ S ∈ F, ∃ N : Matroid (Fin n), N.E = Set.univ ∧ ¬ matroid_connected N ∧
      ∀ S' : Finset (Fin n), S' ≠ S → (N.Indep (S' : Set (Fin n)) ↔ M.Indep (S' : Set (Fin n))))
    (q : ℕ) (hq : q < F.card) : ¬ matroid_connectedness_query_le n q := by
  classical
  rintro ⟨T, hT, hdec⟩
  let o : Finset (Fin n) → Bool := fun S => decide (M.Indep (S : Set (Fin n)))
  have ho : ∀ S : Finset (Fin n), o S = true ↔ M.Indep (S : Set (Fin n)) := fun S => by simp [o]
  have h1 : T.eval o = true := (hdec M hE o ho).2 hM
  obtain ⟨L, hL, hagr⟩ := matroid_indep_query_tree_eval_eq_of_agree o T
  have hlen : L.card < F.card := lt_of_le_of_lt (hL.trans hT) hq
  obtain ⟨S, hSF, hSn⟩ : ∃ S ∈ F, S ∉ L := by
    by_contra hcon
    have hsub : F ⊆ L := fun S hS => by
      by_contra hSL
      exact hcon ⟨S, hS, hSL⟩
    exact absurd (Finset.card_le_card hsub) (not_le.2 hlen)
  obtain ⟨N, hNE, hN, hagree⟩ := hF S hSF
  let o' : Finset (Fin n) → Bool := fun S => decide (N.Indep (S : Set (Fin n)))
  have ho' : ∀ S : Finset (Fin n), o' S = true ↔ N.Indep (S : Set (Fin n)) := fun S => by simp [o']
  have h2 : T.eval o' = T.eval o := hagr o' fun S' hS' => by
    have hne : S' ≠ S := fun h => hSn (h ▸ hS')
    simp only [o, o']
    exact decide_eq_decide.2 (hagree S' hne)
  exact hN ((hdec N hNE o' ho').1 (h2.trans h1))
