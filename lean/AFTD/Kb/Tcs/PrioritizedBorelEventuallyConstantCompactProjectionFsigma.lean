import AFTD.Prelude

/-!
# prioritized_borel_eventually_constant_compact_projection_fsigma

Topic: automata   Node: 6d068688e839

Provenance: helper lemma.

Projecting from a compact hidden-run space the closed compatible-run set restricted to traces eventually equal to a fixed priority gives a countable union of closed branch sets.
-/

theorem prioritized_borel_eventually_constant_compact_projection_fsigma
    {B X P : Type*} [TopologicalSpace B] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace P] [T2Space P] (C : Set (B × X)) (hC : IsClosed C)
    (prio : X → ℕ → P) (hprio : ∀ n, Continuous (fun x => prio x n)) (p : P) :
    ∃ F : ℕ → Set B, (∀ n, IsClosed (F n)) ∧
      {b | ∃ x, (b, x) ∈ C ∧ ∃ N, ∀ n ≥ N, prio x n = p} = ⋃ n, F n := by
  classical
  let E : ℕ → Set (B × X) := fun N =>
    C ∩ {z | ∀ n ≥ N, prio z.2 n = p}
  have hE : ∀ N, IsClosed (E N) := by
    intro N
    apply hC.inter
    have h : {z : B × X | ∀ n ≥ N, prio z.2 n = p} =
        ⋂ n, ⋂ (_ : n ≥ N), {z : B × X | prio z.2 n = p} := by
      ext z
      simp
    rw [h]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro hn
    exact isClosed_eq ((hprio n).comp continuous_snd) continuous_const
  refine ⟨fun N => Prod.fst '' E N, ?_, ?_⟩
  · intro N
    exact isClosedMap_fst_of_compactSpace _ (hE N)
  · ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Prod.exists,
      E, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, N, hN⟩
      exact ⟨N, b, x, ⟨hx, hN⟩, rfl⟩
    · rintro ⟨N, b', x, ⟨hx, hN⟩, hb⟩
      subst b'
      exact ⟨x, hx, N, hN⟩
