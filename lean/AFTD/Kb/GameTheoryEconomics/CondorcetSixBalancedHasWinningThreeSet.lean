import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetSixBalancedTopStructure
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_six_balanced_has_winning_three_set

Topic: social_choice   Node: 724c241ea7ee

Provenance: helper lemma. step towards condorcet_dimension_le_three

Open sub-problem: every six-candidate election with at least one voter in which every three-candidate set contains the top choice of at most half of the voters has a Condorcet winning set of size at most three.
-/

/-- First genuine instance of the balanced regime: six candidates. -/
theorem condorcet_six_balanced_has_winning_three_set (n : ℕ) (P : Fin n → Equiv.Perm (Fin 6))
    (hn : 0 < n)
    (hbal : ∀ S : Finset (Fin 6), S.card = 3 →
      2 * (Finset.univ.filter fun v => (P v).symm ⟨0, by norm_num⟩ ∈ S).card ≤ n) :
    ∃ S : Finset (Fin 6), S.card ≤ 3 ∧ is_condorcet_winning_set P S := by
  classical
  set top : Fin n → Fin 6 := fun v => (P v).symm ⟨0, by norm_num⟩ with htopdef
  set snd : Fin n → Fin 6 := fun v => (P v).symm ⟨1, by norm_num⟩ with hsnddef
  have hstr : ∀ c : Fin 6, 6 * (Finset.univ.filter fun v => top v = c).card = n := by
    intro c
    have := condorcet_six_balanced_top_structure n P hbal c
    simpa only [htopdef] using this
  set k : ℕ := (Finset.univ.filter fun v => top v = 0).card with hkdef
  have hn6 : n = 6 * k := by
    have h0 := hstr 0
    rw [← hkdef] at h0
    omega
  have hkc : ∀ c : Fin 6, (Finset.univ.filter fun v => top v = c).card = k := by
    intro c
    have h := hstr c
    have hgoal : 6 * (Finset.univ.filter fun v => top v = c).card = 6 * k := by omega
    exact Nat.eq_of_mul_eq_mul_left (n := 6) (by norm_num) hgoal
  have hkpos : 0 < k := by omega
  have htop_exists : ∀ c : Fin 6, ∃ v, top v = c := by
    intro c
    have hpos : 0 < (Finset.univ.filter fun v => top v = c).card := by
      rw [hkc c]; exact hkpos
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨v, by simpa using hv⟩
  have hpos_top : ∀ v, P v (top v) = 0 := by intro v; simp [top]
  have hpos_snd : ∀ v, P v (snd v) = 1 := by intro v; simp [snd]
  have hsnd_ne_top : ∀ v, snd v ≠ top v := by
    intro v h
    have h1 := hpos_snd v
    rw [h, hpos_top v] at h1
    simp at h1
  by_cases hwin : ∃ A : Finset (Fin 6), A.card = 3 ∧ is_condorcet_winning_set P A
  · obtain ⟨A, hAc, hw⟩ := hwin
    exact ⟨A, by omega, hw⟩
  · exfalso
    have hwin' : ∀ A : Finset (Fin 6), A.card = 3 → ¬ is_condorcet_winning_set P A := by
      intro A hA hw
      exact hwin ⟨A, hA, hw⟩
    have hA0card : ∀ A : Finset (Fin 6), A.card = 3 →
        (Finset.univ.filter fun v => top v ∉ A).card = 3 * k := by
      intro A hA
      have hdisj : ∀ c ∈ A, ∀ d ∈ A, c ≠ d →
          Disjoint (Finset.univ.filter fun v => top v = c)
            (Finset.univ.filter fun v => top v = d) := by
        intro c _ d _ hcd
        rw [Finset.disjoint_left]
        intro v hv hv'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
        exact hcd (hv.symm.trans hv')
      have hbij : (Finset.univ.filter fun v => top v ∈ A)
          = A.biUnion (fun c => Finset.univ.filter fun v => top v = c) := by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hv => ⟨top v, hv, rfl⟩, fun ⟨c, hc, hvc⟩ => hvc ▸ hc⟩
      have hIn : (Finset.univ.filter fun v => top v ∈ A).card = 3 * k := by
        rw [hbij, Finset.card_biUnion hdisj,
          Finset.sum_congr rfl (fun c (_ : c ∈ A) => hkc c), Finset.sum_const, hA]
        simp
      have hcompl : (Finset.univ.filter fun v => top v ∉ A)
          = Finset.univ \ (Finset.univ.filter fun v => top v ∈ A) := by
        ext v; simp
      rw [hcompl, Finset.card_sdiff, Finset.inter_univ, hIn, Finset.card_univ, Fintype.card_fin]
      omega
    have hwit : ∀ A : Finset (Fin 6), A.card = 3 → ∃ a, a ∉ A ∧
        ∀ v, top v ∉ A → ∀ b ∈ A, P v a < P v b := by
      intro A hA
      have hnot := hwin' A hA
      have hA0c : (Finset.univ.filter fun v => top v ∉ A).card = 3 * k := hA0card A hA
      have hbadIn : ∀ a, (Finset.univ.filter fun v => ∀ b ∈ A, P v a < P v b)
          ⊆ (Finset.univ.filter fun v => top v ∉ A) := by
        intro a v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        intro htopA
        have h1 : P v a < P v (top v) := hv (top v) htopA
        rw [hpos_top v] at h1
        exact absurd h1 (not_lt.mpr (Fin.zero_le (P v a)))
      have hex : ∃ a, a ∉ A ∧
          n ≤ 2 * (Finset.univ.filter fun v => ∀ b ∈ A, P v a < P v b).card := by
        by_contra hc
        apply hnot
        unfold is_condorcet_winning_set
        intro a ha
        by_contra hlt
        exact hc ⟨a, ha, by omega⟩
      obtain ⟨a, haA, hge⟩ := hex
      refine ⟨a, haA, ?_⟩
      have hcard : (Finset.univ.filter fun v => top v ∉ A).card ≤
          (Finset.univ.filter fun v => ∀ b ∈ A, P v a < P v b).card := by
        rw [hA0c]; omega
      have heq : (Finset.univ.filter fun v => ∀ b ∈ A, P v a < P v b)
          = (Finset.univ.filter fun v => top v ∉ A) :=
        Finset.eq_of_subset_of_card_le (hbadIn a) hcard
      intro v hv b hb
      have hmem : v ∈ Finset.univ.filter (fun w => ∀ b ∈ A, P w a < P w b) := by
        rw [heq]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem b hb
    have hkey1 : ∀ (A : Finset (Fin 6)) (a : Fin 6), A.card = 3 → a ∉ A →
        (∀ v, top v ∉ A → ∀ b ∈ A, P v a < P v b) →
        ∀ v, top v ∉ A → snd v ∈ A → a = top v := by
      intro A a hAc haA hdom v htv hsv
      have h1 : P v a < P v (snd v) := hdom v htv (snd v) hsv
      rw [hpos_snd v] at h1
      have hval : ((P v a) : ℕ) = 0 := by
        have h2 : ((P v a) : ℕ) < 1 := by
          have h3 := h1
          rw [Fin.lt_def] at h3
          simpa using h3
        omega
      have h0 : P v a = 0 := Fin.ext (by simpa using hval)
      refine (P v).injective ?_
      rw [h0, hpos_top v]
    have hpair : ∀ v w : Fin n, top v ≠ top w → snd v = top w ∨ snd w = top v := by
      intro v w hne
      by_contra hcon
      push_neg at hcon
      obtain ⟨hvw, hwv⟩ := hcon
      have hs1 : snd v ≠ top v := hsnd_ne_top v
      have hs2 : snd w ≠ top w := hsnd_ne_top w
      set B : Finset (Fin 6) := Finset.univ \ {top v, top w} with hBdef
      have hBcard : B.card = 4 := by
        have h2 : ({top v, top w} : Finset (Fin 6)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using hne)]
          simp
        rw [hBdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h2]
      have hsB : snd v ∈ B := by
        rw [hBdef]
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          not_or, true_and]
        exact ⟨hs1, hvw⟩
      have hwB : snd w ∈ B := by
        rw [hBdef]
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          not_or, true_and]
        exact ⟨hwv, hs2⟩
      have hsmall : ({snd v, snd w} : Finset (Fin 6)).card < B.card := by
        have h2 : ({snd v, snd w} : Finset (Fin 6)).card ≤ 2 := by
          have h3 := Finset.card_insert_le (snd v) ({snd w} : Finset (Fin 6))
          simpa using h3
        omega
      obtain ⟨c, hcB, hc2⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
      have hcv : snd v ≠ c := by
        intro h
        apply hc2
        rw [← h]
        exact Finset.mem_insert_self (snd v) {snd w}
      have hcw : snd w ≠ c := by
        intro h
        apply hc2
        rw [← h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (snd w))
      have htvB : top v ∉ B := by rw [hBdef]; simp
      have htwB : top w ∉ B := by rw [hBdef]; simp
      have hAcard : (B.erase c).card = 3 := by
        rw [Finset.card_erase_of_mem hcB, hBcard]
      obtain ⟨a, haA, hdom⟩ := hwit (B.erase c) hAcard
      have htvA : top v ∉ B.erase c := fun h => htvB (Finset.erase_subset c B h)
      have htwA : top w ∉ B.erase c := fun h => htwB (Finset.erase_subset c B h)
      have hsvA : snd v ∈ B.erase c := by
        rw [Finset.mem_erase]; exact ⟨hcv, hsB⟩
      have hswA : snd w ∈ B.erase c := by
        rw [Finset.mem_erase]; exact ⟨hcw, hwB⟩
      have hav : a = top v := hkey1 (B.erase c) a hAcard haA hdom v htvA hsvA
      have haw : a = top w := hkey1 (B.erase c) a hAcard haA hdom w htwA hswA
      exact hne (hav.symm.trans haw)
    obtain ⟨v0, hv0⟩ := htop_exists 0
    have hs0ne : snd v0 ≠ 0 := by
      have h := hsnd_ne_top v0
      rwa [hv0] at h
    obtain ⟨t', t'', ht'0, ht'2, ht''0, ht''2, ht'ne⟩ : ∃ t' t'' : Fin 6,
        t' ≠ 0 ∧ t' ≠ snd v0 ∧ t'' ≠ 0 ∧ t'' ≠ snd v0 ∧ t' ≠ t'' := by
      have hBc : ((Finset.univ : Finset (Fin 6)) \ {0, snd v0}).card = 4 := by
        have h2 : ({0, snd v0} : Finset (Fin 6)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using hs0ne.symm)]
          simp
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h2]
      have h2 : 1 < ((Finset.univ : Finset (Fin 6)) \ {0, snd v0}).card := by
        rw [hBc]; norm_num
      obtain ⟨t', ht', t'', ht'', hne⟩ := Finset.one_lt_card.mp h2
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        not_or, true_and] at ht' ht''
      exact ⟨t', t'', ht'.1, ht'.2, ht''.1, ht''.2, hne⟩
    obtain ⟨w', hw'⟩ := htop_exists t'
    obtain ⟨w'', hw''⟩ := htop_exists t''
    have hw'0 : snd w' = 0 := by
      have hne : top v0 ≠ top w' := by rw [hv0, hw']; exact ht'0.symm
      rcases hpair v0 w' hne with h | h
      · rw [hw'] at h
        exact absurd h.symm ht'2
      · rwa [hv0] at h
    have hw''0 : snd w'' = 0 := by
      have hne : top v0 ≠ top w'' := by rw [hv0, hw'']; exact ht''0.symm
      rcases hpair v0 w'' hne with h | h
      · rw [hw''] at h
        exact absurd h.symm ht''2
      · rwa [hv0] at h
    have hne' : top w' ≠ top w'' := by rw [hw', hw'']; exact ht'ne
    rcases hpair w' w'' hne' with h | h
    · rw [hw'0, hw''] at h
      exact ht''0 h.symm
    · rw [hw''0, hw'] at h
      exact ht'0 h.symm
