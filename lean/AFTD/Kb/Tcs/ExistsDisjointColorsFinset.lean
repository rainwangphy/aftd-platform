import AFTD.Prelude

/-!
# exists_disjoint_colors_finset

Topic: graphs   Node: 1e6a03494dae

Provenance: helper lemma. arXiv:2611.03151 Lemma 9 proof, Step 1

For any list assignment L on a finite vertex set V with colors in ℕ and any natural number m, there exists an m-element subset Q ⊂ ℕ that is disjoint from the union of all lists L(v) over v ∈ V.
-/

/-- For any vertex-indexed collection of finite lists in ℕ on a finite vertex set, there exists an m-element set of colors disjoint from all lists. -/
theorem exists_disjoint_colors_finset {V : Type*} [Fintype V] (L : V → Finset ℕ) (m : ℕ) :
    ∃ Q : Finset ℕ, Q.card = m ∧ Disjoint Q (Finset.biUnion Finset.univ L) := by
  let S := Finset.biUnion Finset.univ L
  let k := S.sup id + 1
  use Finset.Ico k (k + m)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  · rw [Finset.disjoint_left]
    intro x hx hxS
    rw [Finset.mem_Ico] at hx
    have hle : id x ≤ S.sup id := Finset.le_sup hxS
    dsimp at hle
    omega
