import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame
import AFTD.Kb.GameTheoryEconomics.AGGameLipschitz
import AFTD.Kb.GameTheoryEconomics.AgCnt
import AFTD.Kb.GameTheoryEconomics.AGGamePureNE
import AFTD.Kb.GameTheoryEconomics.AgCntSum
import AFTD.Kb.GameTheoryEconomics.AgY2

/-!
# ag_two_upper

Topic: equilibria   Node: 7b1cb641f2d6

Upper bound for two strategies. Every λ-Lipschitz anonymous game with two strategies (any number of players) has a 2λ-approximate pure Nash equilibrium.
-/

open Finset in
/-- **Upper bound for two strategies.** Every `λ`-Lipschitz anonymous game with two strategies (any number of players) has a `2λ`-approximate pure Nash equilibrium. -/
theorem ag_two_upper {n : ℕ} (G : AGGame n 2) (lam : ℚ) (hlam : 0 ≤ lam)
    (hL : G.Lipschitz lam) :
    ∃ σ : Fin n → Fin 2, G.PureNE (2 * lam) σ := by
  -- payoff advantage of strategy 1 when `k` others play 1
  set d : Fin n → ℕ → ℚ := fun p k => G.u p 1 (agY2 n k) - G.u p 0 (agY2 n k) with hd
  have hsumY : ∀ k, k ≤ n - 1 → ∑ j, agY2 n k j = n - 1 := by
    intro k hk
    simp [agY2, Fin.sum_univ_two]; omega
  -- one step of `k` moves each payoff by at most `2λ`
  have hstep : ∀ p i k, k + 1 ≤ n - 1 →
      |G.u p i (agY2 n (k + 1)) - G.u p i (agY2 n k)| ≤ 2 * lam := by
    intro p i k hk
    have := hL p i (agY2 n (k + 1)) (agY2 n k) (hsumY _ hk) (hsumY _ (by omega))
    have hl1 : ∑ j, |((agY2 n (k + 1) j : ℕ) : ℚ) - (agY2 n k j : ℚ)| = 2 := by
      simp only [Fin.sum_univ_two, agY2]
      simp only [show (0 : Fin 2) ≠ 1 by decide, if_false, if_true]
      have h1 : ((n - 1 - (k + 1) : ℕ) : ℚ) = (n : ℚ) - 1 - k - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have h2 : ((n - 1 - k : ℕ) : ℚ) = (n : ℚ) - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [h1, h2]; push_cast
      rw [show (n : ℚ) - 1 - k - 1 - (n - 1 - k) = -1 by ring,
        show ((k : ℚ) + 1 - k) = 1 by ring]
      norm_num
    rw [hl1] at this; linarith
  set A : ℕ → Finset (Fin n) := fun m => Finset.univ.filter (fun p => m < n ∧ 2 * lam < d p m)
    with hA
  set B : ℕ → Finset (Fin n) :=
    fun m => Finset.univ.filter (fun p => 0 < m ∧ d p (m - 1) < -(2 * lam)) with hB
  have hex : ∃ m, (A m).card ≤ m := ⟨n, by
    have : A n = ∅ := by
      ext p; simp [hA]
    rw [this]; simp⟩
  classical
  set m := Nat.find hex with hm
  have hmA : (A m).card ≤ m := Nat.find_spec hex
  have hmn : m ≤ n := Nat.find_min' hex (by
    have : A n = ∅ := by ext p; simp [hA]
    rw [this]; simp)
  have hB_le : (B m).card ≤ n - m := by
    by_cases h0 : m = 0
    · have : B m = ∅ := by ext p; simp [hB, h0]
      rw [this]; simp
    · have hlt : ¬ (A (m - 1)).card ≤ m - 1 := Nat.find_min hex (by omega)
      have hdisj : Disjoint (A (m - 1)) (B m) := by
        rw [Finset.disjoint_filter]
        intro p _ h1 h2
        linarith [h1.2, h2.2]
      have := Finset.card_union_of_disjoint hdisj
      have := Finset.card_le_univ (A (m - 1) ∪ B m)
      simp only [Fintype.card_fin] at this
      omega
  have hAB : Disjoint (A m) (B m) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    have hm1 : m - 1 + 1 = m := by omega
    have := hstep p 1 (m - 1) (by omega)
    have h0 := hstep p 0 (m - 1) (by omega)
    rw [hm1] at this h0
    have e1 := (abs_le.1 this).2
    have e2 := (abs_le.1 h0).1
    have : d p m - d p (m - 1) ≤ 4 * lam := by
      simp only [hd]; linarith
    linarith [h1.2, h2.2]
  -- choose the set `S` of players on strategy 1
  have hsub : A m ⊆ Finset.univ \ B m := by
    intro p hp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact Finset.disjoint_left.1 hAB hp
  have hcardt : m ≤ (Finset.univ \ B m).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨S, hAS, hSB, hScard⟩ := Finset.exists_subsuperset_card_eq hsub hmA hcardt
  refine ⟨fun p => if p ∈ S then 1 else 0, ?_⟩
  intro p j
  -- the count vector seen by `p`
  have hc1 : agCnt (fun q => if q ∈ S then (1 : Fin 2) else 0) p 1 = (S.erase p).card := by
    unfold agCnt; congr 1; ext q; by_cases hq : q ∈ S <;> simp [hq, and_comm]
  have hsum := agCnt_sum (fun q => if q ∈ S then (1 : Fin 2) else 0) p
  rw [Fin.sum_univ_two] at hsum
  by_cases hp : p ∈ S
  · have hk : (S.erase p).card = m - 1 := by rw [Finset.card_erase_of_mem hp, hScard]
    have hm0 : 0 < m := by
      rw [← hScard]; exact Finset.card_pos.2 ⟨p, hp⟩
    have hcnt : agCnt (fun q => if q ∈ S then (1 : Fin 2) else 0) p = agY2 n (m - 1) := by
      funext i
      fin_cases i
      · simp [agY2]; rw [hc1, hk] at hsum; omega
      · simp [agY2]; rw [hc1, hk]
    have hpB : p ∉ B m := fun h => (Finset.mem_sdiff.1 (hSB hp)).2 h
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hpB
    have := hpB hm0
    simp only [hp, if_true, hcnt]
    fin_cases j
    · simp only [hd] at this; simp; linarith
    · simp; linarith
  · have hk : (S.erase p).card = m := by rw [Finset.erase_eq_of_notMem hp, hScard]
    have hmlt : m < n := by
      have : S ⊆ Finset.univ.erase p := fun q hq => Finset.mem_erase.2 ⟨fun e => hp (e ▸ hq), mem_univ _⟩
      have hle := Finset.card_le_card this
      rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin,
        hScard] at hle
      have := p.isLt
      omega
    have hcnt : agCnt (fun q => if q ∈ S then (1 : Fin 2) else 0) p = agY2 n m := by
      funext i
      fin_cases i
      · simp [agY2]; rw [hc1, hk] at hsum; omega
      · simp [agY2]; rw [hc1, hk]
    have hpA : p ∉ A m := fun h => hp (hAS h)
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hpA
    have := hpA hmlt
    simp only [hp, if_false, hcnt]
    fin_cases j
    · simp; linarith
    · simp only [hd] at this; simp; linarith
