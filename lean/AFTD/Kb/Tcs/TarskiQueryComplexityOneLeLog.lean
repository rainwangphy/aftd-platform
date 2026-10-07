import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryComplexityLe
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryTreeCost

/-!
# tarski_query_complexity_one_le_log

Topic: algorithms   Node: 5d11fe7bcccf

Provenance: formalization of a published result. Source: arXiv:2610.07055 (Tarski fixed points in quasi-FPT queries), Sec. 1 (the binary search baseline, which the recursive algorithm giving O(log^k n) builds on); the case k = 1

One-dimensional Tarski by binary search: for n ≥ 1, a fixed point of any monotone map on the chain {0, …, n−1} can be found with at most ⌊log₂ n⌋ + 1 queries.
-/

/-- The point `min i m` of the chain `{0, …, m}`, as a point of `[m+1]^1`. -/
def tarski_one_pt (m i : ℕ) : Fin 1 → Fin (m + 1) := fun _ => ⟨min i m, by omega⟩

/-- Binary search on `[lo, hi]` with `d` levels of fuel. -/
def tarski_one_bs (m : ℕ) : ℕ → ℕ → ℕ → TarskiQueryTree (m + 1) 1
  | 0, lo, _ => .output (tarski_one_pt m lo)
  | d + 1, lo, hi =>
    .query (tarski_one_pt m ((lo + hi) / 2)) (fun y =>
      if (y 0 : ℕ) = (lo + hi) / 2 then .output (tarski_one_pt m ((lo + hi) / 2))
      else if (y 0 : ℕ) < (lo + hi) / 2 then tarski_one_bs m d lo ((lo + hi) / 2 - 1)
      else tarski_one_bs m d ((lo + hi) / 2 + 1) hi)

theorem tarski_one_pt_val (m i : ℕ) (j : Fin 1) : ((tarski_one_pt m i j : Fin (m + 1)) : ℕ) = min i m :=
  rfl

theorem tarski_one_pt_mono (m : ℕ) {i j : ℕ} (h : i ≤ j) : tarski_one_pt m i ≤ tarski_one_pt m j := by
  intro x
  show ((tarski_one_pt m i x : Fin (m + 1)) : ℕ) ≤ tarski_one_pt m j x
  simp only [tarski_one_pt_val]
  omega

theorem tarski_one_eq_pt (m i : ℕ) (hi : i ≤ m) (x : Fin 1 → Fin (m + 1)) (h : (x 0 : ℕ) = i) :
    x = tarski_one_pt m i := by
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  apply Fin.ext
  rw [h, tarski_one_pt_val]
  omega

theorem tarski_one_bs_spec (m : ℕ) (f : (Fin 1 → Fin (m + 1)) → (Fin 1 → Fin (m + 1)))
    (hf : Monotone f) :
    ∀ d lo hi, lo ≤ hi → hi ≤ m → hi - lo + 1 < 2 ^ (d + 1) →
      lo ≤ (f (tarski_one_pt m lo) 0 : ℕ) → (f (tarski_one_pt m hi) 0 : ℕ) ≤ hi →
      f ((tarski_one_bs m d lo hi).run f) = (tarski_one_bs m d lo hi).run f ∧
        (tarski_one_bs m d lo hi).cost f ≤ d + 1 := by
  have hmono : ∀ {i j : ℕ}, i ≤ j →
      (f (tarski_one_pt m i) 0 : ℕ) ≤ f (tarski_one_pt m j) 0 :=
    fun h => hf (tarski_one_pt_mono m h) 0
  intro d
  induction d with
  | zero =>
    intro lo hi hlh hhm hsz hlo hhi
    have : hi = lo := by simp at hsz; omega
    subst this
    refine ⟨?_, ?_⟩
    · simp only [tarski_one_bs, TarskiQueryTree.run]
      exact tarski_one_eq_pt m hi hhm _ (by omega)
    · simp [tarski_one_bs, TarskiQueryTree.cost]
  | succ d ih =>
    intro lo hi hlh hhm hsz hlo hhi
    have hP : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    by_cases h1 : (f (tarski_one_pt m ((lo + hi) / 2)) 0 : ℕ) = (lo + hi) / 2
    · simp only [tarski_one_bs, TarskiQueryTree.run, TarskiQueryTree.cost, h1, if_true]
      exact ⟨tarski_one_eq_pt m _ (by omega) _ h1, by omega⟩
    by_cases h2 : (f (tarski_one_pt m ((lo + hi) / 2)) 0 : ℕ) < (lo + hi) / 2
    · have hl : lo ≤ (f (tarski_one_pt m ((lo + hi) / 2)) 0 : ℕ) :=
        le_trans hlo (hmono (by omega))
      have := ih lo ((lo + hi) / 2 - 1) (by omega) (by omega) (by omega) hlo
        (by have := hmono (show (lo + hi) / 2 - 1 ≤ (lo + hi) / 2 by omega); omega)
      simp only [tarski_one_bs, TarskiQueryTree.run, TarskiQueryTree.cost, h1, h2, if_false,
        if_true]
      exact ⟨this.1, by omega⟩
    · have hh : (f (tarski_one_pt m ((lo + hi) / 2)) 0 : ℕ) ≤ hi := le_trans (hmono (by omega)) hhi
      have := ih ((lo + hi) / 2 + 1) hi (by omega) hhm (by omega)
        (by have := hmono (show (lo + hi) / 2 ≤ (lo + hi) / 2 + 1 by omega); omega) hhi
      simp only [tarski_one_bs, TarskiQueryTree.run, TarskiQueryTree.cost, h1, h2, if_false]
      exact ⟨this.1, by omega⟩

theorem tarski_query_complexity_one_le_log (n : ℕ) (hn : 1 ≤ n) :
    tarski_query_complexity_le n 1 (Nat.log 2 n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨tarski_one_bs m (Nat.log 2 (m + 1)) 0 m, fun f hf => ?_⟩
  have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (m + 1)
  exact tarski_one_bs_spec m f hf _ 0 m (Nat.zero_le _) le_rfl (by omega) (Nat.zero_le _)
    (by have := (f (tarski_one_pt m m) 0).isLt; omega)
