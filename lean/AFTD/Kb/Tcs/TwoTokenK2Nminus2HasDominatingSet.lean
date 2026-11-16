import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.TwoTokenKmnLlVertex
import AFTD.Kb.Tcs.TwoTokenKmnLrVertex

/-!
# two_token_k2_nminus2_has_dominating_set

Topic: graphs   Node: f333046f7325

Provenance: helper lemma. arXiv:2611.15124 Proposition 3.1 -- Domination in token graphs of graphs with domination number two

For every integer n ≥ 4, there exists a dominating set of the 2-token graph F_2(K_{2,n-2}) of cardinality at most n - 2.
-/

lemma two_token_k2_nminus2_has_dominating_set_finset_card_two_cases {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset (A ⊕ B)) (hs : s.card = 2) :
    (∃ a1 a2 : A, a1 ≠ a2 ∧ s = {Sum.inl a1, Sum.inl a2}) ∨
    (∃ (a : A) (b : B), s = {Sum.inl a, Sum.inr b}) ∨
    (∃ b1 b2 : B, b1 ≠ b2 ∧ s = {Sum.inr b1, Sum.inr b2}) := by
  rw [Finset.card_eq_two] at hs
  rcases hs with ⟨x, y, hne, rfl⟩
  rcases x with a1 | b1 <;> rcases y with a2 | b2
  · left
    refine ⟨a1, a2, ?_, rfl⟩
    rintro rfl; exact hne rfl
  · right; left; exact ⟨a1, b2, rfl⟩
  · right; left; refine ⟨a2, b1, ?_⟩; rw [Finset.pair_comm]
  · right; right
    refine ⟨b1, b2, ?_, rfl⟩
    rintro rfl; exact hne rfl

lemma two_token_k2_nminus2_has_dominating_set_fin2_pair_eq {k : ℕ} (a1 a2 : Fin 2) (hne : a1 ≠ a2) :
    ({Sum.inl a1, Sum.inl a2} : Finset (Fin 2 ⊕ Fin k)) =
    {Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2)} := by
  revert hne
  fin_cases a1 <;> fin_cases a2
  · intro h; contradiction
  · intro _; rfl
  · intro _; rw [Finset.pair_comm]; rfl
  · intro h; contradiction

/-- The 2-token graph F_2(K_{2,n-2}) has a dominating set of cardinality at most n - 2. -/
theorem two_token_k2_nminus2_has_dominating_set (n : ℕ) (hn : 4 ≤ n) :
    ∃ S : Finset { s : Finset (Fin 2 ⊕ Fin (n - 2)) // s.card = 2 },
      simple_graph_is_dominating (token_graph (completeBipartiteGraph (Fin 2) (Fin (n - 2))) 2) (S : Set _) ∧
      S.card ≤ n - 2 := by
  have hk : 0 < n - 2 := by omega
  let z : Fin (n - 2) := ⟨0, hk⟩
  let ll : { s : Finset (Fin 2 ⊕ Fin (n - 2)) // s.card = 2 } :=
    two_token_kmn_ll_vertex (0 : Fin 2) (1 : Fin 2) (by decide)
  let lr_part := (Finset.univ.erase z).image (fun j => two_token_kmn_lr_vertex (0 : Fin 2) j)
  let S : Finset { s : Finset (Fin 2 ⊕ Fin (n - 2)) // s.card = 2 } := insert ll lr_part
  refine ⟨S, ?_, ?_⟩
  · intro v
    rcases two_token_k2_nminus2_has_dominating_set_finset_card_two_cases v.val v.property with
      (⟨a1, a2, hne, hs⟩ | ⟨a, b, hs⟩ | ⟨b1, b2, hne, hs⟩)
    · -- Case LL
      left
      have h_eq : v = ll := by
        apply Subtype.ext
        dsimp [ll, two_token_kmn_ll_vertex]
        rw [hs]
        exact two_token_k2_nminus2_has_dominating_set_fin2_pair_eq a1 a2 hne
      rw [h_eq]
      exact Finset.mem_insert_self _ _
    · -- Case LR
      fin_cases a
      · -- a = 0
        by_cases hb : b = z
        · -- b = z
          subst hb
          right
          refine ⟨ll, Finset.mem_insert_self _ _, ?_⟩
          refine ⟨Sum.inl (1 : Fin 2), Sum.inr z, ?_, ?_⟩
          · dsimp [completeBipartiteGraph]; left; simp
          · ext x
            simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
            rw [hs]
            dsimp [ll, two_token_kmn_ll_vertex]
            aesop
        · -- b ≠ z
          left
          have h_eq : v = two_token_kmn_lr_vertex (0 : Fin 2) b := by
            apply Subtype.ext
            exact hs
          rw [h_eq]
          apply Finset.mem_insert_of_mem
          dsimp [lr_part]
          apply Finset.mem_image_of_mem
          simp [hb]
      · -- a = 1
        right
        refine ⟨ll, Finset.mem_insert_self _ _, ?_⟩
        refine ⟨Sum.inl (0 : Fin 2), Sum.inr b, ?_, ?_⟩
        · dsimp [completeBipartiteGraph]; left; simp
        · ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
          rw [hs]
          dsimp [ll, two_token_kmn_ll_vertex]
          aesop
    · -- Case RR
      right
      by_cases hb1 : b1 = z
      · have hb2 : b2 ≠ z := by intro h; subst h; subst hb1; exact hne rfl
        let u := two_token_kmn_lr_vertex (0 : Fin 2) b2
        have hu : u ∈ S := by
          apply Finset.mem_insert_of_mem
          dsimp [lr_part]
          apply Finset.mem_image_of_mem
          simp [hb2]
        refine ⟨u, hu, ?_⟩
        refine ⟨Sum.inl (0 : Fin 2), Sum.inr b1, ?_, ?_⟩
        · dsimp [completeBipartiteGraph]; left; simp
        · ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
          rw [hs]
          dsimp [u, two_token_kmn_lr_vertex]
          aesop
      · let u := two_token_kmn_lr_vertex (0 : Fin 2) b1
        have hu : u ∈ S := by
          apply Finset.mem_insert_of_mem
          dsimp [lr_part]
          apply Finset.mem_image_of_mem
          simp [hb1]
        refine ⟨u, hu, ?_⟩
        refine ⟨Sum.inl (0 : Fin 2), Sum.inr b2, ?_, ?_⟩
        · dsimp [completeBipartiteGraph]; left; simp
        · ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
          rw [hs]
          dsimp [u, two_token_kmn_lr_vertex]
          aesop
  · have h1 : S.card ≤ lr_part.card + 1 := Finset.card_insert_le ll lr_part
    have h2 : lr_part.card ≤ (Finset.univ.erase z).card := Finset.card_image_le
    have h3 : (Finset.univ.erase z).card = (n - 2) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    omega
