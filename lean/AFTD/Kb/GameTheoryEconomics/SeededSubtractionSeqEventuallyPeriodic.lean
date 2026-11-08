import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SeededSubtractionSeq
import AFTD.Kb.GameTheoryEconomics.IsEventualPeriod
import AFTD.Kb.Tcs.G

/-!
# seeded_subtraction_seq_eventually_periodic

Topic: combinatorial_games   Node: 9dd03829dd08

Provenance: formalization of a published result. Source: knowledgebase, OP-1251

For every integer $a \ge 1$ and every binary initial seed of length $2a + 1$, the generated subtraction sequence is eventually periodic.
-/

private def seeded_subtraction_seq_eventually_periodic_step (a : ℕ) (ha : 1 ≤ a) :
    (Fin (2 * a + 1) → Bool) → (Fin (2 * a + 1) → Bool) :=
  fun b i =>
    if h : (i : ℕ) + 1 < 2 * a + 1 then b ⟨(i : ℕ) + 1, h⟩
    else !b ⟨a + 1, by omega⟩ || !b ⟨1, by omega⟩ || !b ⟨0, by omega⟩

private def seeded_subtraction_seq_eventually_periodic_block (a : ℕ)
    (seed : Fin (2 * a + 1) → Bool) (n : ℕ) : Fin (2 * a + 1) → Bool :=
  fun i => seeded_subtraction_seq a seed (n + i.val)

private lemma seeded_subtraction_seq_eventually_periodic_rec (a : ℕ)
    (seed : Fin (2 * a + 1) → Bool) (ha : a ≠ 0) (n : ℕ) (hn : 2 * a + 1 ≤ n) :
    seeded_subtraction_seq a seed n =
      (!seeded_subtraction_seq a seed (n - a) ||
        !seeded_subtraction_seq a seed (n - 2 * a) ||
        !seeded_subtraction_seq a seed (n - (2 * a + 1))) := by
  rw [seeded_subtraction_seq.eq_def]
  dsimp only
  rw [dif_neg (by omega : ¬ n < 2 * a + 1), dif_neg ha]

private lemma seeded_subtraction_seq_eventually_periodic_initial (a : ℕ)
    (seed : Fin (2 * a + 1) → Bool) (i : Fin (2 * a + 1)) :
    seeded_subtraction_seq a seed i.val = seed i := by
  rw [seeded_subtraction_seq.eq_def]
  simp only [show i.val < 2 * a + 1 from i.isLt, dif_pos]

private lemma seeded_subtraction_seq_eventually_periodic_block_zero (a : ℕ)
    (seed : Fin (2 * a + 1) → Bool) :
    seeded_subtraction_seq_eventually_periodic_block a seed 0 = seed := by
  funext i
  simp only [seeded_subtraction_seq_eventually_periodic_block, Nat.zero_add]
  exact seeded_subtraction_seq_eventually_periodic_initial a seed i

private lemma seeded_subtraction_seq_eventually_periodic_block_succ (a : ℕ) (ha : 1 ≤ a)
    (seed : Fin (2 * a + 1) → Bool) (n : ℕ) :
    seeded_subtraction_seq_eventually_periodic_block a seed (n + 1) =
      seeded_subtraction_seq_eventually_periodic_step a ha
        (seeded_subtraction_seq_eventually_periodic_block a seed n) := by
  funext i
  simp only [seeded_subtraction_seq_eventually_periodic_step,
    seeded_subtraction_seq_eventually_periodic_block]
  by_cases h : (i : ℕ) + 1 < 2 * a + 1
  · rw [dif_pos h]
    rw [show n + 1 + (i : ℕ) = n + ((i : ℕ) + 1) from by omega]
  · rw [dif_neg h]
    have hi : (i : ℕ) = 2 * a := by have := i.isLt; omega
    rw [hi]
    rw [show n + 1 + 2 * a = n + (2 * a + 1) from by omega]
    rw [seeded_subtraction_seq_eventually_periodic_rec a seed (by omega) (n + (2 * a + 1)) (by omega)]
    rw [show n + (2 * a + 1) - a = n + (a + 1) from by omega,
        show n + (2 * a + 1) - 2 * a = n + 1 from by omega,
        show n + (2 * a + 1) - (2 * a + 1) = n + 0 from by omega]

private lemma seeded_subtraction_seq_eventually_periodic_block_iterate (a : ℕ) (ha : 1 ≤ a)
    (seed : Fin (2 * a + 1) → Bool) (n : ℕ) :
    seeded_subtraction_seq_eventually_periodic_block a seed n =
      (seeded_subtraction_seq_eventually_periodic_step a ha)^[n] seed := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, id_eq]
    exact seeded_subtraction_seq_eventually_periodic_block_zero a seed
  | succ n ih =>
    rw [seeded_subtraction_seq_eventually_periodic_block_succ a ha seed n, ih,
      Function.iterate_succ_apply']

private lemma seeded_subtraction_seq_eventually_periodic_finite_orbit
    {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ p N : ℕ, 0 < p ∧ ∀ n ≥ N, f^[n + p] x = f^[n] x := by
  classical
  let N := Fintype.card α
  let g : Fin (N + 1) → α := fun k => f^[k.val] x
  have hcard : Fintype.card α < Fintype.card (Fin (N + 1)) := by simp [N]
  obtain ⟨x0, y0, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  obtain ⟨i, j, hij, hper⟩ : ∃ i j : ℕ, i < j ∧ f^[i] x = f^[j] x := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨x0.val, y0.val, hlt, heq⟩
    · exact ⟨y0.val, x0.val, hgt, heq.symm⟩
  refine ⟨j - i, i, by omega, ?_⟩
  have hij' : i + (j - i) = j := by omega
  have hclaim : ∀ k : ℕ, f^[i + k] x = f^[i + k + (j - i)] x := by
    intro k
    induction k with
    | zero => simpa [hij'] using hper
    | succ k ih =>
      have h1 : i + (k + 1) = i + k + 1 := by omega
      have h2 : i + k + 1 + (j - i) = i + k + (j - i) + 1 := by omega
      rw [h1, h2, Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  intro n hn
  have hn' : n = i + (n - i) := by omega
  rw [hn']
  exact (hclaim (n - i)).symm

/-- Every seed generates an eventually periodic binary sequence in the {a, 2a, 2a+1} subtraction game. -/
theorem seeded_subtraction_seq_eventually_periodic (a : ℕ) (ha : 1 ≤ a)
    (seed : Fin (2 * a + 1) → Bool) :
    ∃ p : ℕ, is_eventual_period (seeded_subtraction_seq a seed) p := by
  obtain ⟨p, N, hp, hN⟩ :=
    seeded_subtraction_seq_eventually_periodic_finite_orbit
      (seeded_subtraction_seq_eventually_periodic_step a ha) seed
  refine ⟨p, hp, N, ?_⟩
  intro n hn
  let z : Fin (2 * a + 1) := ⟨0, by omega⟩
  have key : (seeded_subtraction_seq_eventually_periodic_step a ha)^[n + p] seed
      = (seeded_subtraction_seq_eventually_periodic_step a ha)^[n] seed := hN n hn
  have hb : seeded_subtraction_seq_eventually_periodic_block a seed n
      = (seeded_subtraction_seq_eventually_periodic_step a ha)^[n] seed :=
    seeded_subtraction_seq_eventually_periodic_block_iterate a ha seed n
  have hbp : seeded_subtraction_seq_eventually_periodic_block a seed (n + p)
      = (seeded_subtraction_seq_eventually_periodic_step a ha)^[n + p] seed :=
    seeded_subtraction_seq_eventually_periodic_block_iterate a ha seed (n + p)
  calc seeded_subtraction_seq a seed (n + p)
      = (seeded_subtraction_seq_eventually_periodic_block a seed (n + p)) z := by
        simp [seeded_subtraction_seq_eventually_periodic_block, z]
    _ = ((seeded_subtraction_seq_eventually_periodic_step a ha)^[n + p] seed) z := by
        rw [hbp]
    _ = ((seeded_subtraction_seq_eventually_periodic_step a ha)^[n] seed) z := by
        rw [key]
    _ = (seeded_subtraction_seq_eventually_periodic_block a seed n) z := by
        rw [hb]
    _ = seeded_subtraction_seq a seed n := by
        simp [seeded_subtraction_seq_eventually_periodic_block, z]
