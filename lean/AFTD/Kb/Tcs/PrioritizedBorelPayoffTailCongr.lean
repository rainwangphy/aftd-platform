import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_payoff_tail_congr

Topic: automata   Node: 9fd117d307e7

Provenance: helper lemma. Hidden-choice strategy compression related to arXiv:2611.10136, Conjecture 19.

Two prioritized-game plays have the same payoff when their directions agree everywhere and their priorities agree eventually.
-/

theorem op1385_ofFn_prefix {A : Type} (f : ℕ → A) {n m : ℕ} (h : n ≤ m) :
    List.ofFn (fun i : Fin n => f i) <+: List.ofFn (fun i : Fin m => f i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.ofFn_add]
  exact List.prefix_append _ _

theorem op1385_nested_histories_tail {A : Type} (histories : ℕ → List A)
    (actual : ℕ → A) (K : ℕ) (hlen : ∀ n, (histories n).length = n)
    (hnest : ∀ n ≥ K, histories (n+1) = histories n ++ [actual n]) :
    ∃ f : ℕ → A, (∀ n ≥ K, List.ofFn (fun i : Fin n => f i) = histories n) ∧
      (∀ n ≥ K, f n = actual n) := by
  classical
  let f : ℕ → A := fun n => if hn : n < K then
    (histories K).get ⟨n, by simpa [hlen K] using hn⟩ else actual n
  have htail : ∀ n ≥ K, f n = actual n := by
    intro n hn
    simp [f, Nat.not_lt.mpr hn]
  have hbase : List.ofFn (fun i : Fin K => f i) = histories K := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hi'
      have hiK : i < K := by simpa using hi
      simp [f, hiK]
  have hsucc (n : ℕ) : List.ofFn (fun i : Fin (n+1) => f i) =
      List.ofFn (fun i : Fin n => f i) ++ [f n] := by
    simpa only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
      (List.ofFn_succ' (fun i : Fin (n+1) => f i))
  have hall : ∀ m, List.ofFn (fun i : Fin (K + m) => f i) = histories (K + m) := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      have hs := hnest (K + m) (by omega)
      have ht := htail (K + m) (by omega)
      change List.ofFn (fun i : Fin ((K+m)+1) => f i) = histories ((K+m)+1)
      rw [hsucc, ih, ht]
      exact hs.symm
  refine ⟨f, ?_, htail⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hall m

theorem op1385_nested_histories_visible_shadow {A : Type} (vis : A → Bool)
    (histories : ℕ → List A) (actual : ℕ → A) (K : ℕ)
    (hlen : ∀ n, (histories n).length = n)
    (hvis : ∀ n, (histories n).map vis = List.ofFn (fun i : Fin n => vis (actual i)))
    (hnest : ∀ n ≥ K, histories (n+1) = histories n ++ [actual n]) :
    ∃ f : ℕ → A, (∀ n ≥ K, List.ofFn (fun i : Fin n => f i) = histories n) ∧
      (∀ n ≥ K, f n = actual n) ∧ ∀ n, vis (f n) = vis (actual n) := by
  obtain ⟨f, hprefix, htail⟩ := op1385_nested_histories_tail histories actual K hlen hnest
  refine ⟨f, hprefix, htail, ?_⟩
  intro n
  by_cases hn : n < K
  · have hmap := congrArg (List.map vis) (hprefix K (le_refl K))
    have hlist : List.ofFn (fun i : Fin K => vis (f i)) =
        List.ofFn (fun i : Fin K => vis (actual i)) := by
      simpa only [List.map_ofFn, Function.comp_def, hvis K] using hmap
    have hf := List.ofFn_injective hlist
    exact congrFun hf ⟨n, hn⟩
  · rw [htail n (by omega)]

def op1385Payoff {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (π : ℕ → TreeGameEdge Q k) : Prop :=
  ∃ p : Fin k, Filter.Frequently (fun n => (π n).prio = p) Filter.atTop ∧
    (∀ q : Fin k, p < q → ¬ Filter.Frequently (fun n => (π n).prio = q) Filter.atTop) ∧
    (fun n => (π n).dir) ∈ G.winning_sets p

theorem prioritized_borel_payoff_tail_congr {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k)
    (π ρ : ℕ → TreeGameEdge Q k)
    (hdir : ∀ n, (π n).dir = (ρ n).dir)
    (hprio : ∀ᶠ n in Filter.atTop, (π n).prio = (ρ n).prio) :
    op1385Payoff G π ↔ op1385Payoff G ρ := by
  have hfreq (p : Fin k) :
      Filter.Frequently (fun n => (π n).prio = p) Filter.atTop ↔
      Filter.Frequently (fun n => (ρ n).prio = p) Filter.atTop :=
    Filter.frequently_congr (hprio.mono (fun n hn => by rw [hn]))
  have hbranch : (fun n => (π n).dir) = (fun n => (ρ n).dir) := funext hdir
  constructor
  · rintro ⟨p, hp, hmax, hb⟩
    refine ⟨p, (hfreq p).mp hp, ?_, ?_⟩
    · intro q hq hqfreq
      exact hmax q hq ((hfreq q).mpr hqfreq)
    · simpa only [← hbranch] using hb
  · rintro ⟨p, hp, hmax, hb⟩
    refine ⟨p, (hfreq p).mpr hp, ?_, ?_⟩
    · intro q hq hqfreq
      exact hmax q hq ((hfreq q).mp hqfreq)
    · simpa only [hbranch] using hb
