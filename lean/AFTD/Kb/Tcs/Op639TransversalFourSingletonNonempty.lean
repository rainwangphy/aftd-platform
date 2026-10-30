import AFTD.Prelude

/-!
# op_639_transversal_four_singleton_nonempty

Topic: combinatorics   Node: 46ff2b7adcd3

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

For any minimal transversal T of size 4 in a hypergraph with covering number at least 4, and any element x in T, there exists an edge e in F such that e ∩ T = {x}.
-/

/-- For any minimal transversal T of size 4 in a hypergraph with tau >= 4, and any x in T, there is an edge meeting T in {x}. -/
theorem op_639_transversal_four_singleton_nonempty
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (htau_ge : ∀ T : Finset V, T.card < 4 → ∃ e ∈ F, Disjoint e T)
    (T : Finset V) (hT : T.card = 4) (hT_trans : ∀ e ∈ F, ¬Disjoint e T)
    (x : V) (hx : x ∈ T) :
    ∃ e ∈ F, e ∩ T = {x} := by
  have hcard : (T.erase x).card < 4 := by
    rw [Finset.card_erase_of_mem hx, hT]
    norm_num
  obtain ⟨e, heF, he_disj⟩ := htau_ge (T.erase x) hcard
  have huniq : ∀ y, y ∈ e ∩ T → y = x := by
    intro y hy
    rw [Finset.mem_inter] at hy
    by_contra hne
    have hyerase : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hne, hy.2⟩
    exact (Finset.disjoint_left.mp he_disj hy.1) hyerase
  have hnonempty : (e ∩ T).Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp (hT_trans e heF)
  obtain ⟨y, hy⟩ := hnonempty
  have hxy : x ∈ e ∩ T := by
    simpa [huniq y hy] using hy
  refine ⟨e, heF, ?_⟩
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hxy, huniq⟩
