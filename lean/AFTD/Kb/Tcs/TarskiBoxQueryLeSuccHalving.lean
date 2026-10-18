import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiQueryTreeBind
import AFTD.Kb.Tcs.TarskiQueryTreeBindSpec
import AFTD.Kb.Tcs.TarskiQueryTreeSliceLift
import AFTD.Kb.Tcs.TarskiQueryTreeSliceLiftSpec
import AFTD.Kb.Tcs.TarskiBoxQueryLeSmall
import AFTD.Kb.Tcs.TarskiSliceLowerBound
import AFTD.Kb.Tcs.TarskiSliceUpperBound
import AFTD.Kb.Tcs.TarskiSubintervalSliceShrink
import AFTD.Kb.Tcs.TarskiSliceSubboxMonotoneAndFixed
import AFTD.Kb.Tcs.TarskiSubintervalFixedPoint
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.G

/-!
# tarski_box_query_le_succ_halving

Topic: algorithms   Node: b103af7e3712

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

One dimension costs a factor log₂ n: from a box-search algorithm in dimension k with q queries one gets one in dimension k+1 with at most 3·(k+1)·(log₂ n + 2)·(q+1) + 2^(k+1) queries.
-/

open Finset
set_option maxHeartbeats 2000000

/-- Potential of a box: the sum over coordinates of `clog 2` of the coordinate gap. -/
def tarski_box_query_le_succ_halving_pot (n K : ℕ) (a b : Fin K → Fin n) : ℕ :=
  ∑ j : Fin K, Nat.clog 2 ((b j : ℕ) - (a j))

/-- A box that shrinks in every coordinate has no larger potential. -/
theorem tarski_box_query_le_succ_halving_pot_lt (n K : ℕ) {u u' v v' : Fin K → Fin n}
    (huu' : u ≤ u') (hvv' : v' ≤ v) (i : Fin K)
    (hi : Nat.clog 2 ((v' i : ℕ) - (u' i)) < Nat.clog 2 ((v i : ℕ) - (u i))) :
    tarski_box_query_le_succ_halving_pot n K u' v' <
      tarski_box_query_le_succ_halving_pot n K u v := by
  unfold tarski_box_query_le_succ_halving_pot
  apply Finset.sum_lt_sum
  · intro j _
    refine Nat.clog_mono (b := 2) (c := 2) (by norm_num) (le_refl 2) ?_
    have h1 : (u j : ℕ) ≤ (u' j : ℕ) := huu' j
    have h2 : (v' j : ℕ) ≤ (v j : ℕ) := hvv' j
    omega
  · exact ⟨i, Finset.mem_univ i, hi⟩

/-- Halving strictly decreases `clog 2` for gaps of size at least two. -/
theorem tarski_box_query_le_succ_halving_clog_half_lt {d : ℕ} (hd : 2 ≤ d) :
    Nat.clog 2 (d / 2) < Nat.clog 2 d := by
  have hb : 1 < 2 := by norm_num
  set m := Nat.clog 2 d with hm
  have hmpos : 0 < m := Nat.clog_pos hb (by omega)
  have hd2 : d ≤ 2 ^ m := (Nat.clog_le_iff_le_pow hb).mp (le_refl m)
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Nat.pow_succ]
  have hle : d / 2 ≤ 2 ^ (m - 1) := by
    rw [hpow] at hd2
    omega
  have := (Nat.clog_le_iff_le_pow hb).mpr hle
  omega

/-- The complementary half also strictly decreases `clog 2` for gaps of size at least two. -/
theorem tarski_box_query_le_succ_halving_clog_sub_half_lt {d : ℕ} (hd : 2 ≤ d) :
    Nat.clog 2 (d - d / 2) < Nat.clog 2 d := by
  have hb : 1 < 2 := by norm_num
  set m := Nat.clog 2 d with hm
  have hmpos : 0 < m := Nat.clog_pos hb (by omega)
  have hd2 : d ≤ 2 ^ m := (Nat.clog_le_iff_le_pow hb).mp (le_refl m)
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Nat.pow_succ]
  have hle : d - d / 2 ≤ 2 ^ (m - 1) := by
    rw [hpow] at hd2
    omega
  have := (Nat.clog_le_iff_le_pow hb).mpr hle
  omega

/-- An `insertNth` point stays inside the box when the slice and the cut do. -/
theorem tarski_box_query_le_succ_halving_insertNth_mem (n k : ℕ) (a b : Fin (k+1) → Fin n)
    (i : Fin (k+1)) (c : Fin n) (hac : a i ≤ c) (hcb : c ≤ b i)
    (y : Fin k → Fin n) (ha'y : (a ∘ i.succAbove) ≤ y) (hyb' : y ≤ (b ∘ i.succAbove)) :
    a ≤ i.insertNth c y ∧ i.insertNth c y ≤ b := by
  refine ⟨?_, ?_⟩
  · rw [Fin.le_insertNth_iff]
    exact ⟨hac, ha'y⟩
  · rw [Fin.insertNth_le_iff]
    exact ⟨hcb, hyb'⟩

/-- A bisection step strictly decreases the potential in both resulting sub-boxes. -/
theorem tarski_box_query_le_succ_halving_pot_step (n k : ℕ) (a b : Fin (k+1) → Fin n)
    (i : Fin (k+1)) (c : Fin n)
    (hac : a i ≤ c) (hcb : c ≤ b i)
    (hstep : 2 ≤ (b i : ℕ) - (a i))
    (hc : (c : ℕ) - (a i : ℕ) = ((b i : ℕ) - (a i)) / 2)
    (y : Fin k → Fin n) (ha'y : (a ∘ i.succAbove) ≤ y) (hyb' : y ≤ (b ∘ i.succAbove)) :
    tarski_box_query_le_succ_halving_pot n (k+1) (i.insertNth c y) b <
      tarski_box_query_le_succ_halving_pot n (k+1) a b ∧
    tarski_box_query_le_succ_halving_pot n (k+1) a (i.insertNth c y) <
      tarski_box_query_le_succ_halving_pot n (k+1) a b := by
  obtain ⟨hax, hxb⟩ := tarski_box_query_le_succ_halving_insertNth_mem n k a b i c hac hcb y ha'y hyb'
  have hxi : (i.insertNth c y : Fin (k+1) → Fin n) i = c := by simp
  have hd : 2 ≤ (b i : ℕ) - (a i) := hstep
  constructor
  · refine tarski_box_query_le_succ_halving_pot_lt n (k+1) (u := a) (u' := i.insertNth c y)
      (v := b) (v' := b) hax (le_refl b) i ?_
    rw [hxi]
    have hb1 : (c : ℕ) ≤ (b i : ℕ) := hcb
    have hb2 : (a i : ℕ) ≤ (c : ℕ) := hac
    have : (b i : ℕ) - (c : ℕ) = ((b i : ℕ) - (a i)) - ((b i : ℕ) - (a i)) / 2 := by omega
    rw [this]
    exact tarski_box_query_le_succ_halving_clog_sub_half_lt hd
  · refine tarski_box_query_le_succ_halving_pot_lt n (k+1) (u := a) (u' := a) (v := b)
      (v' := i.insertNth c y) (le_refl a) hxb i ?_
    rw [hxi]
    have : (c : ℕ) - (a i : ℕ) = ((b i : ℕ) - (a i)) / 2 := hc
    rw [this]
    exact tarski_box_query_le_succ_halving_clog_half_lt hd

/-- Brute-force query tree: query the listed points in order, output the first fixed point. -/
def tarski_box_query_le_succ_halving_brute {n K : ℕ} (dflt : Fin K → Fin n) :
    List (Fin K → Fin n) → TarskiQueryTree n K
  | [] => TarskiQueryTree.output dflt
  | x :: xs =>
    TarskiQueryTree.query x (fun v => if v = x then TarskiQueryTree.output x else
      tarski_box_query_le_succ_halving_brute dflt xs)

/-- The brute-force tree finds a fixed point contained in the list, within `length` queries. -/
theorem tarski_box_query_le_succ_halving_brute_spec {n K : ℕ} (dflt : Fin K → Fin n)
    (L : List (Fin K → Fin n))
    (f : (Fin K → Fin n) → Fin K → Fin n) (hL : ∃ x ∈ L, f x = x) :
    TarskiQueryTree.run f (tarski_box_query_le_succ_halving_brute dflt L) ∈ L ∧
    f (TarskiQueryTree.run f (tarski_box_query_le_succ_halving_brute dflt L)) =
      TarskiQueryTree.run f (tarski_box_query_le_succ_halving_brute dflt L) ∧
    TarskiQueryTree.cost f (tarski_box_query_le_succ_halving_brute dflt L) ≤ L.length := by
  induction L with
  | nil => simp at hL
  | cons x xs ih =>
    obtain ⟨w, hw, hfw⟩ := hL
    rw [List.mem_cons] at hw
    simp only [tarski_box_query_le_succ_halving_brute, TarskiQueryTree.run.eq_2,
      TarskiQueryTree.cost.eq_2]
    by_cases hfx : f x = x
    · rw [if_pos hfx, TarskiQueryTree.run.eq_1, TarskiQueryTree.cost.eq_1]
      exact ⟨List.mem_cons_self, hfx, by simp⟩
    · rw [if_neg hfx]
      have hL' : ∃ y ∈ xs, f y = y := by
        rcases hw with rfl | hw
        · exact absurd hfw hfx
        · exact ⟨w, hw, hfw⟩
      obtain ⟨h1, h2, h3⟩ := ih hL'
      refine ⟨List.mem_cons_of_mem _ h1, h2, ?_⟩
      simp only [List.length_cons]
      omega

/-- One bisection step: slice, lift, query the lifted point, and dispatch to the
sub-box promised by monotonicity, giving the potential-decrease cost bound. -/
theorem tarski_box_query_le_succ_halving_step (n k q m : ℕ) [NeZero n]
    (h : tarski_box_query_le n k q)
    (ih : ∀ m' < m, ∀ (a b : Fin (k+1) → Fin n), a ≤ b →
      tarski_box_query_le_succ_halving_pot n (k+1) a b ≤ m' →
      ∃ t : TarskiQueryTree n (k+1),
        ∀ f : (Fin (k+1) → Fin n) → Fin (k+1) → Fin n,
          Monotone f → a ≤ f a → f b ≤ b →
            a ≤ TarskiQueryTree.run f t ∧ TarskiQueryTree.run f t ≤ b ∧
            f (TarskiQueryTree.run f t) = TarskiQueryTree.run f t ∧
            TarskiQueryTree.cost f t ≤
              tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1))
    (a b : Fin (k+1) → Fin n) (hab : a ≤ b)
    (hpot : tarski_box_query_le_succ_halving_pot n (k+1) a b ≤ m)
    (i : Fin (k+1)) (hstep : 2 ≤ (b i : ℕ) - (a i)) :
    ∃ t : TarskiQueryTree n (k+1),
      ∀ f : (Fin (k+1) → Fin n) → Fin (k+1) → Fin n,
        Monotone f → a ≤ f a → f b ≤ b →
          a ≤ TarskiQueryTree.run f t ∧ TarskiQueryTree.run f t ≤ b ∧
          f (TarskiQueryTree.run f t) = TarskiQueryTree.run f t ∧
          TarskiQueryTree.cost f t ≤
            tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1) := by
  classical
  have hcval_lt : (a i : ℕ) + ((b i : ℕ) - (a i)) / 2 < n := by
    have hbn : (b i : ℕ) < n := Fin.is_lt (b i)
    have hdle : ((b i : ℕ) - (a i)) / 2 ≤ (b i : ℕ) - (a i) := Nat.div_le_self _ _
    omega
  set c : Fin n := ⟨(a i : ℕ) + ((b i : ℕ) - (a i)) / 2, hcval_lt⟩ with hcdef
  have hcval : (c : ℕ) = (a i : ℕ) + ((b i : ℕ) - (a i)) / 2 := by rw [hcdef]
  have hac : a i ≤ c := by rw [Fin.le_def, hcval]; omega
  have hcb : c ≤ b i := by rw [Fin.le_def, hcval]; omega
  obtain ⟨tq, htq⟩ := h (a ∘ i.succAbove) (b ∘ i.succAbove) (fun j => hab (i.succAbove j))
  let T : ∀ (u v : Fin (k+1) → Fin n), u ≤ v →
      tarski_box_query_le_succ_halving_pot n (k+1) u v < m → TarskiQueryTree n (k+1) :=
    fun u v huv hp => Classical.choose
      (ih (tarski_box_query_le_succ_halving_pot n (k+1) u v) hp u v huv (le_refl _))
  have hTspec : ∀ (u v : Fin (k+1) → Fin n) (huv : u ≤ v)
      (hp : tarski_box_query_le_succ_halving_pot n (k+1) u v < m),
      ∀ f : (Fin (k+1) → Fin n) → Fin (k+1) → Fin n, Monotone f → u ≤ f u → f v ≤ v →
        u ≤ TarskiQueryTree.run f (T u v huv hp) ∧
        TarskiQueryTree.run f (T u v huv hp) ≤ v ∧
        f (TarskiQueryTree.run f (T u v huv hp)) = TarskiQueryTree.run f (T u v huv hp) ∧
        TarskiQueryTree.cost f (T u v huv hp) ≤
          tarski_box_query_le_succ_halving_pot n (k+1) u v * (q + 1) + 2 ^ (k+1) := by
    intro u v huv hp f hf hu hv
    exact Classical.choose_spec
      (ih (tarski_box_query_le_succ_halving_pot n (k+1) u v) hp u v huv (le_refl _)) f hf hu hv
  let g : (Fin (k+1) → Fin n) → TarskiQueryTree n (k+1) := fun w =>
    if hw : a ≤ w ∧ w ≤ b ∧ tarski_box_query_le_succ_halving_pot n (k+1) w b < m ∧
        tarski_box_query_le_succ_halving_pot n (k+1) a w < m then
      TarskiQueryTree.query w (fun v =>
        if v i = w i then TarskiQueryTree.output w
        else if w i < v i then T w b hw.2.1 hw.2.2.1
        else T a w hw.1 hw.2.2.2)
    else TarskiQueryTree.output w
  refine ⟨tarski_query_tree_bind g (tarski_query_tree_slice_lift i c tq), ?_⟩
  intro f hf ha hb
  obtain ⟨hg_mono, hga, hgb, hglift⟩ :=
    tarski_slice_subbox_monotone_and_fixed n k f hf a b ha hb i c hac hcb
  obtain ⟨hya, hyb, hyfix, hycost⟩ :=
    htq (fun y j => f (i.insertNth c y) (i.succAbove j)) hg_mono hga hgb
  set y : Fin k → Fin n := TarskiQueryTree.run (fun y j => f (i.insertNth c y) (i.succAbove j)) tq
    with hydef
  set x : Fin (k+1) → Fin n := i.insertNth c y with hxdef
  obtain ⟨hax, hxb, hxsliced⟩ := hglift y hya hyb hyfix
  have hrun_lift : TarskiQueryTree.run f (tarski_query_tree_slice_lift i c tq) = x := by
    rw [(tarski_query_tree_slice_lift_spec i c f tq).1]
  have hcost_lift : TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) =
      TarskiQueryTree.cost (fun y j => f (i.insertNth c y) (i.succAbove j)) tq :=
    (tarski_query_tree_slice_lift_spec i c f tq).2
  have hlq : TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) ≤ q := by
    rw [hcost_lift]; exact hycost
  have hpstep := tarski_box_query_le_succ_halving_pot_step n k a b i c hac hcb hstep
    (by rw [hcval]; omega) y hya hyb
  have hpotx1 : tarski_box_query_le_succ_halving_pot n (k+1) x b < m :=
    lt_of_lt_of_le hpstep.1 hpot
  have hpotx2 : tarski_box_query_le_succ_halving_pot n (k+1) a x < m :=
    lt_of_lt_of_le hpstep.2 hpot
  have hguard : a ≤ x ∧ x ≤ b ∧ tarski_box_query_le_succ_halving_pot n (k+1) x b < m ∧
      tarski_box_query_le_succ_halving_pot n (k+1) a x < m := ⟨hax, hxb, hpotx1, hpotx2⟩
  have hgx : g x = TarskiQueryTree.query x (fun v =>
      if v i = x i then TarskiQueryTree.output x
      else if x i < v i then T x b hguard.2.1 hguard.2.2.1
      else T a x hguard.1 hguard.2.2.2) := by
    simp only [g]
    rw [dif_pos hguard]
  have hpotpos : 1 ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b := by
    have hpos : 0 < Nat.clog 2 ((b i : ℕ) - (a i)) := Nat.clog_pos (by norm_num) (by omega)
    have := Finset.single_le_sum
      (f := fun j : Fin (k+1) => Nat.clog 2 ((b j : ℕ) - (a j)))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    unfold tarski_box_query_le_succ_halving_pot
    omega
  have hbs := tarski_query_tree_bind_spec g f (tarski_query_tree_slice_lift i c tq)
  have key : a ≤ TarskiQueryTree.run f (g x) ∧ TarskiQueryTree.run f (g x) ≤ b ∧
      f (TarskiQueryTree.run f (g x)) = TarskiQueryTree.run f (g x) ∧
      TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) + TarskiQueryTree.cost f (g x)
        ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1) := by
    by_cases h1 : f x i = x i
    · have hrun1 : TarskiQueryTree.run f (g x) = x := by
        rw [hgx, TarskiQueryTree.run.eq_2, if_pos h1, TarskiQueryTree.run.eq_1]
      have hcost1 : TarskiQueryTree.cost f (g x) = 1 := by
        rw [hgx, TarskiQueryTree.cost.eq_2, if_pos h1, TarskiQueryTree.cost.eq_1]
      have hfixx : f x = x := by
        funext j
        rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨t, ht⟩
        · rw [hji]; exact h1
        · rw [ht]
          exact hxsliced _ (Fin.succAbove_ne i t)
      refine ⟨by rw [hrun1]; exact hax, by rw [hrun1]; exact hxb, by rw [hrun1]; exact hfixx, ?_⟩
      rw [hcost1]
      have h1' : TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) + 1 ≤ q + 1 := by omega
      have h2' : q + 1 ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) := by
        calc q + 1 = 1 * (q + 1) := by ring
          _ ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) :=
              Nat.mul_le_mul_right _ hpotpos
      exact le_trans h1' (le_trans h2' (Nat.le_add_right _ _))
    · by_cases h2 : x i < f x i
      · have hrun2 : TarskiQueryTree.run f (g x) =
            TarskiQueryTree.run f (T x b hguard.2.1 hguard.2.2.1) := by
          rw [hgx, TarskiQueryTree.run.eq_2, if_neg h1, if_pos h2]
        have hcost2 : TarskiQueryTree.cost f (g x) =
            TarskiQueryTree.cost f (T x b hguard.2.1 hguard.2.2.1) + 1 := by
          rw [hgx, TarskiQueryTree.cost.eq_2, if_neg h1, if_pos h2]
        have hxfx : x ≤ f x := by
          intro j
          rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨t, ht⟩
          · rw [hji]; exact le_of_lt h2
          · rw [ht]; rw [hxsliced _ (Fin.succAbove_ne i t)]
        obtain ⟨hT1, hT2, hT3, hT4⟩ := hTspec x b hxb hpotx1 f hf hxfx hb
        refine ⟨by rw [hrun2]; exact le_trans hax hT1, by rw [hrun2]; exact hT2,
          by rw [hrun2]; exact hT3, ?_⟩
        rw [hcost2]
        have hp3 : tarski_box_query_le_succ_halving_pot n (k+1) x b + 1 ≤
            tarski_box_query_le_succ_halving_pot n (k+1) a b := by
          rw [hxdef]; exact hpstep.1
        calc TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) +
              (TarskiQueryTree.cost f (T x b hguard.2.1 hguard.2.2.1) + 1)
            ≤ q + ((tarski_box_query_le_succ_halving_pot n (k+1) x b * (q + 1) + 2 ^ (k+1))
                + 1) := by omega
          _ = (tarski_box_query_le_succ_halving_pot n (k+1) x b + 1) * (q + 1) + 2 ^ (k+1) := by
              ring
          _ ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1) := by
              apply Nat.add_le_add_right
              exact Nat.mul_le_mul_right _ hp3
      · have h3 : f x i < x i := lt_of_le_of_ne (le_of_not_gt h2) h1
        have hrun3 : TarskiQueryTree.run f (g x) =
            TarskiQueryTree.run f (T a x hguard.1 hguard.2.2.2) := by
          rw [hgx, TarskiQueryTree.run.eq_2, if_neg h1, if_neg h2]
        have hcost3 : TarskiQueryTree.cost f (g x) =
            TarskiQueryTree.cost f (T a x hguard.1 hguard.2.2.2) + 1 := by
          rw [hgx, TarskiQueryTree.cost.eq_2, if_neg h1, if_neg h2]
        have hfxx : f x ≤ x := by
          intro j
          rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨t, ht⟩
          · rw [hji]; exact le_of_lt h3
          · rw [ht]; rw [hxsliced _ (Fin.succAbove_ne i t)]
        obtain ⟨hT1, hT2, hT3, hT4⟩ := hTspec a x hax hpotx2 f hf ha hfxx
        refine ⟨by rw [hrun3]; exact hT1, by rw [hrun3]; exact le_trans hT2 hxb,
          by rw [hrun3]; exact hT3, ?_⟩
        rw [hcost3]
        have hp3 : tarski_box_query_le_succ_halving_pot n (k+1) a x + 1 ≤
            tarski_box_query_le_succ_halving_pot n (k+1) a b := by
          rw [hxdef]; exact hpstep.2
        calc TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c tq) +
              (TarskiQueryTree.cost f (T a x hguard.1 hguard.2.2.2) + 1)
            ≤ q + ((tarski_box_query_le_succ_halving_pot n (k+1) a x * (q + 1) + 2 ^ (k+1))
                + 1) := by omega
          _ = (tarski_box_query_le_succ_halving_pot n (k+1) a x + 1) * (q + 1) + 2 ^ (k+1) := by
              ring
          _ ≤ tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1) := by
              apply Nat.add_le_add_right
              exact Nat.mul_le_mul_right _ hp3
  obtain ⟨k1, k2, k3, k4⟩ := key
  exact ⟨by rw [hbs.1, hrun_lift]; exact k1,
         by rw [hbs.1, hrun_lift]; exact k2,
         by rw [hbs.1, hrun_lift]; exact k3,
         by rw [hbs.2, hrun_lift]; exact k4⟩

/-- Main induction: every box admits a tree with cost at most `Φ · (q+1) + 2^(k+1)`. -/
theorem tarski_box_query_le_succ_halving_aux (n k q : ℕ) [NeZero n]
    (h : tarski_box_query_le n k q) :
    ∀ (m : ℕ) (a b : Fin (k+1) → Fin n), a ≤ b →
      tarski_box_query_le_succ_halving_pot n (k+1) a b ≤ m →
      ∃ t : TarskiQueryTree n (k+1),
        ∀ f : (Fin (k+1) → Fin n) → Fin (k+1) → Fin n,
          Monotone f → a ≤ f a → f b ≤ b →
            a ≤ TarskiQueryTree.run f t ∧ TarskiQueryTree.run f t ≤ b ∧
            f (TarskiQueryTree.run f t) = TarskiQueryTree.run f t ∧
            TarskiQueryTree.cost f t ≤
              tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) + 2 ^ (k+1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b hab hpot
    by_cases hsmall : ∀ i : Fin (k+1), (b i : ℕ) - (a i) ≤ 1
    · refine ⟨tarski_box_query_le_succ_halving_brute a (Finset.Icc a b).toList, ?_⟩
      intro f hf ha hb
      obtain ⟨x0, hx0a, hx0b, hx0f⟩ := tarski_subinterval_fixed_point n (k+1) f hf a b hab ha hb
      have hL : ∃ y ∈ (Finset.Icc a b).toList, f y = y :=
        ⟨x0, by rw [Finset.mem_toList, Finset.mem_Icc]; exact ⟨hx0a, hx0b⟩, hx0f⟩
      obtain ⟨h1, h2, h3⟩ := tarski_box_query_le_succ_halving_brute_spec a
        (Finset.Icc a b).toList f hL
      rw [Finset.mem_toList, Finset.mem_Icc] at h1
      refine ⟨h1.1, h1.2, h2, ?_⟩
      have hcard : (Finset.Icc a b).card ≤ 2 ^ (k+1) := by
        rw [Pi.card_Icc]
        calc ∏ i : Fin (k+1), (Finset.Icc (a i) (b i)).card ≤ ∏ _i : Fin (k+1), 2 := by
              apply Finset.prod_le_prod
              · intro i _; simp
              · intro i _
                rw [Fin.card_Icc]
                have h2' := hab i
                have h3' := hsmall i
                omega
          _ = 2 ^ (k+1) := by simp
      rw [Finset.length_toList] at h3
      exact le_trans h3 (le_trans hcard (Nat.le_add_left _ _))
    · obtain ⟨i, hi⟩ := not_forall.mp hsmall
      exact tarski_box_query_le_succ_halving_step n k q m h ih a b hab hpot i (by omega)

/-- Halving recursion: one extra dimension costs a multiplicative factor log₂ n. -/
theorem tarski_box_query_le_succ_halving (n k q : ℕ) [NeZero n]
    (h : tarski_box_query_le n k q) :
    tarski_box_query_le n (k+1) (3 * (k+1) * (Nat.log 2 n + 2) * (q + 1) + 2 ^ (k+1)) := by
  intro a b hab
  obtain ⟨t, ht⟩ := tarski_box_query_le_succ_halving_aux n k q h
    (tarski_box_query_le_succ_halving_pot n (k+1) a b) a b hab (le_refl _)
  refine ⟨t, fun f hf ha hb => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := ht f hf ha hb
  refine ⟨h1, h2, h3, le_trans h4 ?_⟩
  have hpot1 : tarski_box_query_le_succ_halving_pot n (k+1) a b ≤ (k+1) * Nat.clog 2 n := by
    unfold tarski_box_query_le_succ_halving_pot
    calc ∑ j : Fin (k+1), Nat.clog 2 ((b j : ℕ) - (a j)) ≤ ∑ _j : Fin (k+1), Nat.clog 2 n := by
          apply Finset.sum_le_sum
          intro j _
          refine Nat.clog_mono (b := 2) (c := 2) (by norm_num) (le_refl 2) ?_
          have h1' : (b j : ℕ) < n := Fin.is_lt (b j)
          omega
      _ = (k+1) * Nat.clog 2 n := by simp
  have hclog : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
    have hb : 1 < 2 := by norm_num
    rw [Nat.clog_le_iff_le_pow hb]
    exact Nat.le_of_lt (Nat.lt_pow_succ_log_self hb n)
  have hL : tarski_box_query_le_succ_halving_pot n (k+1) a b ≤
      3 * (k+1) * (Nat.log 2 n + 2) := by
    have hstep1 : tarski_box_query_le_succ_halving_pot n (k+1) a b ≤
        (k+1) * (Nat.log 2 n + 1) := le_trans hpot1 (Nat.mul_le_mul_left _ hclog)
    have hstep2 : (k+1) * (Nat.log 2 n + 1) ≤ 3 * (k+1) * (Nat.log 2 n + 2) := by
      have h1' : Nat.log 2 n + 1 ≤ 3 * (Nat.log 2 n + 2) := by omega
      calc (k+1) * (Nat.log 2 n + 1) ≤ (k+1) * (3 * (Nat.log 2 n + 2)) :=
            Nat.mul_le_mul_left _ h1'
        _ = 3 * (k+1) * (Nat.log 2 n + 2) := by ring
    exact le_trans hstep1 hstep2
  have hmul : tarski_box_query_le_succ_halving_pot n (k+1) a b * (q + 1) ≤
      3 * (k+1) * (Nat.log 2 n + 2) * (q + 1) := Nat.mul_le_mul_right _ hL
  exact Nat.add_le_add_right hmul _
