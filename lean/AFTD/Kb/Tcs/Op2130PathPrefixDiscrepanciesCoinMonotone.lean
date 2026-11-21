import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.Op2130PathHeightUpdateMonotone
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_2130_path_prefix_discrepancies_coin_monotone

Topic: online_algorithms   Node: 85766764150d

Provenance: helper lemma. OP-2130: attractive coupling for cumulative path discrepancies

For path requests written left to right, increasing any subset of the tie coins cannot decrease any prefix sum of the discrepancy vector at any time.
-/

def op_2130_path_prefix_discrepancies_coin_monotone_pfx {n : ℕ} (d : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), d i

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_zero {n : ℕ} (d : Fin n → ℤ) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx d 0 = 0 := by
  unfold op_2130_path_prefix_discrepancies_coin_monotone_pfx
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  omega

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_succ {n : ℕ} (d : Fin n → ℤ) {k : ℕ} (hk : k < n) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx d (k+1) =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d k + d ⟨k, hk⟩ := by
  unfold op_2130_path_prefix_discrepancies_coin_monotone_pfx
  have hset : Finset.univ.filter (fun i : Fin n => i.val < k+1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases h' : i.val < k
      · exact Or.inr h'
      · left
        apply Fin.ext
        show i.val = k
        omega
    · intro h
      rcases h with h | h'
      · rw [h]; simp
      · omega
  rw [hset]
  have hnot : ⟨k, hk⟩ ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by
    simp
  rw [Finset.sum_insert hnot]
  ring

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_step {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) (k : ℕ) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e b) k =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d k + (if e.1.val < k then (if b then 1 else -1) else 0)
        + (if e.2.val < k then (if b then -1 else 1) else 0) := by
  unfold op_2130_path_prefix_discrepancies_coin_monotone_pfx carpool_step
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq']; simp
  · rw [Finset.sum_ite_eq']; simp

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) (k : ℕ)
    (h : e.2.val = e.1.val + 1) (hk : k ≤ e.1.val) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e b) k =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d k := by
  rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step]
  have h1 : ¬ e.1.val < k := by omega
  have h2 : ¬ e.2.val < k := by omega
  rw [if_neg h1, if_neg h2]; ring

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) (k : ℕ)
    (h : e.2.val = e.1.val + 1) (hk : e.1.val + 2 ≤ k) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e b) k =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d k := by
  rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step]
  have h1 : e.1.val < k := by omega
  have h2 : e.2.val < k := by omega
  rw [if_pos h1, if_pos h2]
  cases b <;> simp

lemma op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool)
    (h : e.2.val = e.1.val + 1) :
    op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e b) (e.1.val + 1) =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) + (if b then 1 else -1) := by
  rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step]
  have h1 : e.1.val < e.1.val + 1 := by omega
  have h2 : ¬ e.2.val < e.1.val + 1 := by omega
  rw [if_pos h1, if_neg h2]; ring

lemma op_2130_path_prefix_discrepancies_coin_monotone_ite_arith (a b c : ℤ) (coin : Bool) :
    (if a - b < c - a then true else if c - a < a - b then false else coin)
      = (if 2 * a < b + c then true else if b + c < 2 * a then false else coin) := by
  by_cases h1 : a - b < c - a
  · have h2 : 2 * a < b + c := by omega
    simp [h1, h2]
  · have h2 : ¬ 2 * a < b + c := by omega
    by_cases h3 : c - a < a - b
    · have h4 : b + c < 2 * a := by omega
      simp [h1, h2, h3, h4]
    · have h4 : ¬ b + c < 2 * a := by omega
      simp [h1, h2, h3, h4]

lemma op_2130_path_prefix_discrepancies_coin_monotone_greedy_bit_pfx {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (c : Bool)
    (h : e.2.val = e.1.val + 1) :
    (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)
      = (if 2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) <
            op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
            op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 2) then true
         else if op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
              op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 2) <
              2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) then false
         else c) := by
  have hi1 : e.1.val + 1 < n := by have := e.2.isLt; omega
  have hd1 : d e.1 = op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) -
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val := by
    have hh := op_2130_path_prefix_discrepancies_coin_monotone_pfx_succ d (k := e.1.val) e.1.isLt
    change d ⟨e.1.val, e.1.isLt⟩ = op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) -
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val
    rw [hh]; ring
  have hd2 : d e.2 = op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 2) -
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val + 1) := by
    have hh := op_2130_path_prefix_discrepancies_coin_monotone_pfx_succ d (k := e.1.val + 1) hi1
    have he2 : (⟨e.1.val + 1, hi1⟩ : Fin n) = e.2 := by
      apply Fin.ext; show e.1.val + 1 = e.2.val; omega
    rw [show e.1.val + 1 + 1 = e.1.val + 2 by ring] at hh
    rw [← he2]
    rw [hh]; ring
  rw [hd1, hd2, op_2130_path_prefix_discrepancies_coin_monotone_ite_arith]

lemma op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_inc {n : ℕ} (d : Fin n → ℤ) (e : Fin n × Fin n) (c : Bool)
    (h : e.2.val = e.1.val + 1) :
    (if (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c) then (1:ℤ) else -1)
      = (if 2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+1) <
            op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
            op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+2) then 1
         else if op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
              op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+2) <
              2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+1) then -1
         else if c then 1 else -1) := by
  rw [op_2130_path_prefix_discrepancies_coin_monotone_greedy_bit_pfx d e c h]
  by_cases h1 : 2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+1) <
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+2)
  · simp [h1]
  · by_cases h2 : op_2130_path_prefix_discrepancies_coin_monotone_pfx d e.1.val +
        op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+2) <
        2 * op_2130_path_prefix_discrepancies_coin_monotone_pfx d (e.1.val+1)
    · simp [h1, h2]
    · cases c <;> simp [h1, h2]

lemma op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_pfx_le {n : ℕ} (e : Fin n × Fin n) (h : e.2.val = e.1.val + 1)
    (coin coin' : Bool) (d d' : Fin n → ℤ)
    (hc : coin = false ∨ coin' = true)
    (hord : ∀ k, k ≤ n → op_2130_path_prefix_discrepancies_coin_monotone_pfx d k ≤
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d' k)
    (hpar : ∀ k, k ≤ n → op_2130_path_prefix_discrepancies_coin_monotone_pfx d k % 2 =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d' k % 2) :
    ∀ k, k ≤ n →
      op_2130_path_prefix_discrepancies_coin_monotone_pfx
        (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else coin)) k
      ≤ op_2130_path_prefix_discrepancies_coin_monotone_pfx
        (carpool_step n d' e (if d' e.1 < d' e.2 then true else if d' e.2 < d' e.1 then false else coin')) k := by
  intro k hk
  by_cases hlow : k ≤ e.1.val
  · rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low d e _ k h hlow,
        op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low d' e _ k h hlow]
    exact hord k hk
  · by_cases hhigh : e.1.val + 2 ≤ k
    · rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high d e _ k h hhigh,
          op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high d' e _ k h hhigh]
      exact hord k hk
    · have hk_eq : k = e.1.val + 1 := by omega
      subst hk_eq
      rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid d e _ h,
          op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid d' e _ h]
      rw [op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_inc d e coin h,
          op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_inc d' e coin' h]
      exact op_2130_path_height_update_monotone _ _ _ _ _ _ coin coin'
        (hord e.1.val (by have := e.1.isLt; omega))
        (hord (e.1.val+1) (by have := e.2.isLt; omega))
        (hord (e.1.val+2) (by have := e.2.isLt; omega))
        (hpar (e.1.val+1) (by have := e.2.isLt; omega))
        hc

lemma op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_pfx_par {n : ℕ} (e : Fin n × Fin n) (h : e.2.val = e.1.val + 1)
    (b b' : Bool) (d d' : Fin n → ℤ)
    (hpar : ∀ k, k ≤ n → op_2130_path_prefix_discrepancies_coin_monotone_pfx d k % 2 =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d' k % 2) :
    ∀ k, k ≤ n →
      op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d e b) k % 2 =
        op_2130_path_prefix_discrepancies_coin_monotone_pfx (carpool_step n d' e b') k % 2 := by
  intro k hk
  by_cases hlow : k ≤ e.1.val
  · rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low d e _ k h hlow,
        op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_low d' e _ k h hlow]
    exact hpar k hk
  · by_cases hhigh : e.1.val + 2 ≤ k
    · rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high d e _ k h hhigh,
          op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_high d' e _ k h hhigh]
      exact hpar k hk
    · have hk_eq : k = e.1.val + 1 := by omega
      subst hk_eq
      rw [op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid d e b h,
          op_2130_path_prefix_discrepancies_coin_monotone_pfx_step_mid d' e b' h]
      have hp := hpar (e.1.val+1) (by have := e.2.isLt; omega)
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

def op_2130_path_prefix_discrepancies_coin_monotone_statesL (n : ℕ) (edges : List (Fin n × Fin n)) (coins : List Bool) (d : Fin n → ℤ) :
    List (Fin n → ℤ) :=
  List.scanl (fun d x => carpool_step n d x.1 x.2) d (edges.zip (carpool_greedy_orientations.aux n edges coins d))

lemma op_2130_path_prefix_discrepancies_coin_monotone_statesL_cons {n : ℕ} (e : Fin n × Fin n) (es : List (Fin n × Fin n)) (c : Bool) (cs : List Bool) (d : Fin n → ℤ) :
    op_2130_path_prefix_discrepancies_coin_monotone_statesL n (e :: es) (c :: cs) d =
      d :: op_2130_path_prefix_discrepancies_coin_monotone_statesL n es cs
        (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) := by
  unfold op_2130_path_prefix_discrepancies_coin_monotone_statesL
  rw [carpool_greedy_orientations.aux.eq_def]
  simp only [List.zip_cons_cons, List.scanl_cons]

lemma op_2130_path_prefix_discrepancies_coin_monotone_discrepancies_statesL (n : ℕ) (edges : List (Fin n × Fin n)) (coins : List Bool) :
    carpool_discrepancies n edges (carpool_greedy_orientations n edges coins) =
      op_2130_path_prefix_discrepancies_coin_monotone_statesL n edges coins 0 := by
  simp only [carpool_discrepancies, carpool_greedy_orientations,
    op_2130_path_prefix_discrepancies_coin_monotone_statesL]
  rfl

lemma op_2130_path_prefix_discrepancies_coin_monotone_statesL_aux_le
    (n : ℕ) (edges : List (Fin n × Fin n))
    (hpath : ∀ e ∈ edges, e.1.val + 1 = e.2.val)
    (r s : List Bool) (hr : r.length = edges.length) (hs : s.length = edges.length)
    (hcoin : ∀ i, r.getD i false = false ∨ s.getD i true = true)
    (d d' : Fin n → ℤ)
    (hord : ∀ k, k ≤ n → op_2130_path_prefix_discrepancies_coin_monotone_pfx d k ≤
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d' k)
    (hpar : ∀ k, k ≤ n → op_2130_path_prefix_discrepancies_coin_monotone_pfx d k % 2 =
      op_2130_path_prefix_discrepancies_coin_monotone_pfx d' k % 2) :
    ∀ t, t ≤ edges.length → ∀ k, k ≤ n →
      op_2130_path_prefix_discrepancies_coin_monotone_pfx
        ((op_2130_path_prefix_discrepancies_coin_monotone_statesL n edges r d).getD t (fun _ => 0)) k
        ≤ op_2130_path_prefix_discrepancies_coin_monotone_pfx
        ((op_2130_path_prefix_discrepancies_coin_monotone_statesL n edges s d').getD t (fun _ => 0)) k := by
  induction edges generalizing r s d d' with
  | nil =>
    intro t ht k hk
    have hr0 : r = [] := List.length_eq_zero_iff.mp (by simpa using hr)
    have hs0 : s = [] := List.length_eq_zero_iff.mp (by simpa using hs)
    subst hr0; subst hs0
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    simp only [op_2130_path_prefix_discrepancies_coin_monotone_statesL, List.zip_nil_left, List.scanl_nil, List.getD_cons_zero]
    exact hord k hk
  | cons e es ih =>
    intro t ht k hk
    cases r with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hr; omega
    | cons c cs =>
      cases s with
      | nil =>
        simp only [List.length_nil, List.length_cons] at hs; omega
      | cons c' cs' =>
        simp only [List.length_cons] at hr hs
        have hcs : cs.length = es.length := by omega
        have hcs' : cs'.length = es.length := by omega
        have hpath' : ∀ e' ∈ es, e'.1.val + 1 = e'.2.val := by
          intro e' he'; exact hpath e' (List.mem_cons_of_mem e he')
        have hcoin_shift : ∀ i, cs.getD i false = false ∨ cs'.getD i true = true := by
          intro i
          have hh := hcoin (i+1)
          simpa only [List.getD_cons_succ] using hh
        have hc0 : c = false ∨ c' = true := by
          have hh := hcoin 0
          simpa only [List.getD_cons_zero] using hh
        have he : e.2.val = e.1.val + 1 := by
          have := hpath e (List.mem_cons_self); omega
        have hord1 : ∀ k, k ≤ n →
            op_2130_path_prefix_discrepancies_coin_monotone_pfx
              (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) k
            ≤ op_2130_path_prefix_discrepancies_coin_monotone_pfx
              (carpool_step n d' e (if d' e.1 < d' e.2 then true else if d' e.2 < d' e.1 then false else c')) k :=
          op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_pfx_le e he c c' d d' hc0 hord hpar
        have hpar1 : ∀ k, k ≤ n →
            op_2130_path_prefix_discrepancies_coin_monotone_pfx
              (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) k % 2
            = op_2130_path_prefix_discrepancies_coin_monotone_pfx
              (carpool_step n d' e (if d' e.1 < d' e.2 then true else if d' e.2 < d' e.1 then false else c')) k % 2 :=
          op_2130_path_prefix_discrepancies_coin_monotone_greedy_step_pfx_par e he _ _ d d' hpar
        have hcons1 : op_2130_path_prefix_discrepancies_coin_monotone_statesL n (e :: es) (c :: cs) d =
            d :: op_2130_path_prefix_discrepancies_coin_monotone_statesL n es cs
              (carpool_step n d e (if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c)) :=
          op_2130_path_prefix_discrepancies_coin_monotone_statesL_cons e es c cs d
        have hcons2 : op_2130_path_prefix_discrepancies_coin_monotone_statesL n (e :: es) (c' :: cs') d' =
            d' :: op_2130_path_prefix_discrepancies_coin_monotone_statesL n es cs'
              (carpool_step n d' e (if d' e.1 < d' e.2 then true else if d' e.2 < d' e.1 then false else c')) :=
          op_2130_path_prefix_discrepancies_coin_monotone_statesL_cons e es c' cs' d'
        cases t with
        | zero =>
          rw [hcons1, hcons2]
          simp only [List.getD_cons_zero]
          exact hord k hk
        | succ t' =>
          have ht' : t' ≤ es.length := by
            simp only [List.length_cons] at ht
            omega
          rw [hcons1, hcons2]
          simp only [List.getD_cons_succ]
          exact ih hpath' cs cs' hcs hcs' hcoin_shift _ _ hord1 hpar1 t' ht' k hk

theorem op_2130_path_prefix_discrepancies_coin_monotone (n : ℕ) (edges : List (Fin n × Fin n)) (hpath : ∀ e ∈ edges, e.1.val + 1 = e.2.val) (r s : Fin edges.length → Bool) (hcoin : ∀ i, r i = false ∨ s i = true) (t k : ℕ) (ht : t ≤ edges.length) (hk : k ≤ n) : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), ((carpool_discrepancies n edges (carpool_greedy_orientations n edges (List.ofFn r))).getD t (fun _ => 0)) i) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), ((carpool_discrepancies n edges (carpool_greedy_orientations n edges (List.ofFn s))).getD t (fun _ => 0)) i := by
  have hcoin' : ∀ i, (List.ofFn r).getD i false = false ∨ (List.ofFn s).getD i true = true := by
    intro i
    by_cases hi : i < edges.length
    · have h1 : (List.ofFn r).getD i false = r ⟨i, hi⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      have h2 : (List.ofFn s).getD i true = s ⟨i, hi⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      rw [h1, h2]
      exact hcoin ⟨i, hi⟩
    · left
      rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]
  have hres := op_2130_path_prefix_discrepancies_coin_monotone_statesL_aux_le n edges hpath (List.ofFn r) (List.ofFn s)
    (by simp) (by simp) hcoin' (fun _ => 0) (fun _ => 0)
    (fun k _ => le_rfl) (fun k _ => rfl) t ht k hk
  rw [op_2130_path_prefix_discrepancies_coin_monotone_discrepancies_statesL,
      op_2130_path_prefix_discrepancies_coin_monotone_discrepancies_statesL]
  exact hres
