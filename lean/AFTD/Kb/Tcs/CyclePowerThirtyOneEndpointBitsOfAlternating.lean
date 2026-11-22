import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent

/-!
# cycle_power_thirty_one_endpoint_bits_of_alternating

Topic: combinatorics   Node: 8ce8524e6290

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case of the open even case. Endpoint-only classes at exponent 5 from alternation, minus the two middle bits (the hpart hypothesis of cycle_power_thirty_one_middle_bits_of_alternating). SAT cores of window [-16, 16] (experiment 37427) turned into kernel-checked LRAT certificates.

In a tight, exactly dyadically covered, fully covered exponent-5 Boolean class model (offsets 0..31) whose bit 1 alternates, x(p+1,1) = not x(p,1), every class without bit 1 has no inner bit other than possibly the two middle bits 15 and 16. No count hypothesis is needed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

namespace RT1T32

def pz (q : ℕ) : ℤ := (q : ℤ) - 128

def bval (x : ℤ → ℕ → Bool) (i : ℕ) : Bool :=
  if i % 4 = 0 then x (pz (i / 128)) (i / 4 % 32)
  else if i % 4 = 2 then (x (pz (i / 4096)) (i / 128 % 32) && x (pz (i / 4096)) (i / 4 % 32))
  else false

def rval (x : ℤ → ℕ → Bool) : Sat.Valuation := fun i => bval x i = true

def xc (q a : ℕ) : ℕ := 128 * q + 4 * a
def zc (q a b : ℕ) : ℕ := 4096 * q + 128 * a + 4 * b + 2

theorem bval_xc (x : ℤ → ℕ → Bool) (q a : ℕ) (ha : a < 32) : bval x (xc q a) = x (pz q) a := by
  unfold bval xc
  rw [if_pos (by omega)]
  have h1 : (128 * q + 4 * a) / 128 = q := by omega
  have h2 : (128 * q + 4 * a) / 4 % 32 = a := by omega
  rw [h1, h2]

theorem bval_zc (x : ℤ → ℕ → Bool) (q a b : ℕ) (ha : a < 32) (hb : b < 32) :
    bval x (zc q a b) = (x (pz q) a && x (pz q) b) := by
  unfold bval zc
  rw [if_neg (by omega), if_pos (by omega)]
  have h1 : (4096 * q + 128 * a + 4 * b + 2) / 4096 = q := by omega
  have h2 : (4096 * q + 128 * a + 4 * b + 2) / 128 % 32 = a := by omega
  have h3 : (4096 * q + 128 * a + 4 * b + 2) / 4 % 32 = b := by omega
  rw [h1, h2, h3]

theorem pz_sub (q a : ℕ) (h : a ≤ q) : pz (q - a) = pz q - (a : ℤ) := by
  unfold pz; push_cast [Nat.cast_sub h]; ring

theorem fsum_eq (n : ℕ) (g : ℕ → ℕ) : (Finset.range n).sum g = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem neg_sound (f : ℕ → ℕ) (G S : List ℕ) (hG : G.Nodup) (hS : S.Nodup)
    (hsub : ∀ i ∈ S, i ∈ G) (k : ℕ) (hsum : (G.map f).sum ≤ k) (hlen : k < S.length)
    (hall : ∀ i ∈ S, 1 ≤ f i) : False := by
  have h1 : (S.map f).sum ≤ (G.map f).sum := by
    rw [← List.sum_toFinset f hS, ← List.sum_toFinset f hG]
    apply Finset.sum_le_sum_of_subset
    intro i hi; rw [List.mem_toFinset] at hi ⊢; exact hsub i hi
  have h2 : (S.map f).length ≤ (S.map f).sum :=
    List.length_le_sum_of_one_le _ (by
      intro i hi; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi; exact hall j hj)
  rw [List.length_map] at h2
  omega

theorem pos_sound (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (G S : List ℕ) (hG : G.Nodup) (hS : S.Nodup)
    (hsub : ∀ i ∈ S, i ∈ G) (k : ℕ) (hsum : k ≤ (G.map f).sum) (hlen : G.length < S.length + k)
    (hall : ∀ i ∈ S, f i = 0) : False := by
  rw [← List.sum_toFinset f hG] at hsum
  have hsub' : S.toFinset ⊆ G.toFinset := by
    intro i hi; rw [List.mem_toFinset] at hi ⊢; exact hsub i hi
  rw [← Finset.sum_sdiff hsub'] at hsum
  have h0 : ∑ x ∈ S.toFinset, f x = 0 :=
    Finset.sum_eq_zero (fun i hi => hall i (List.mem_toFinset.mp hi))
  have h1 : ∑ x ∈ G.toFinset \ S.toFinset, f x ≤ (G.toFinset \ S.toFinset).card := by
    calc ∑ x ∈ G.toFinset \ S.toFinset, f x ≤ (G.toFinset \ S.toFinset).sum (fun _ => 1) :=
          Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp
  rw [Finset.card_sdiff_of_subset hsub', List.toFinset_card_of_nodup hG,
    List.toFinset_card_of_nodup hS] at h1
  have : S.length ≤ G.length := by
    have := Finset.card_le_card hsub'
    rwa [List.toFinset_card_of_nodup hG, List.toFinset_card_of_nodup hS] at this
  omega

inductive Grp
  | rk (j qv : ℕ)
  | cov (d qv : ℕ)

def Grp.list : Grp → List ℕ
  | .rk j qv => (List.range (2 ^ j)).map (fun a => zc (qv - a) a (a + 32 - 2 ^ j))
  | .cov d qv => (List.range (32 - d)).map (fun a => zc (qv - a) a (a + d))

def Grp.exact : Grp → Bool
  | .cov _ _ => false
  | _ => true

def Grp.valid : Grp → Bool
  | .rk j qv => decide (1 ≤ j ∧ j < 5 ∧ 31 ≤ qv)
  | .cov d qv => decide (1 ≤ d ∧ d < 32 ∧ 31 ≤ qv)

/-- the exponent-five model hypotheses used by the certificate (no count) -/
def Model (x : ℤ → ℕ → Bool) : Prop :=
  (∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
      (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat)) ∧
  (∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1) ∧
  (∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true) ∧
  (∀ p : ℤ, x (p+1) 1 = !x p 1)

section
variable (x : ℤ → ℕ → Bool)

theorem map_rk (j qv : ℕ) (hj : 1 ≤ j) (hj5 : j < 5) (hq : 31 ≤ qv) :
    ((Grp.rk j qv).list.map (fun i => (bval x i).toNat)) =
      (List.range (2 ^ j)).map (fun (a : ℕ) => (x (pz qv - (a : ℤ)) a &&
        x (pz qv - (a : ℤ)) (a + 2 ^ (4+1) - 2 ^ j)).toNat) := by
  have hp : 2 ^ j ≤ 16 := by interval_cases j <;> norm_num
  have hp1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  unfold Grp.list
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  rw [List.mem_range] at ha
  simp only [Function.comp]
  rw [bval_zc x _ _ _ (by omega) (by omega), pz_sub _ _ (by omega)]
  norm_num

theorem map_cov (d qv : ℕ) (hd : d < 32) (hq : 31 ≤ qv) :
    ((Grp.cov d qv).list.map (fun i => (bval x i).toNat)) =
      (List.range (32 - d)).map (fun (a : ℕ) => (x (pz qv - (a : ℤ)) a &&
        x (pz qv - (a : ℤ)) (a + d)).toNat) := by
  unfold Grp.list
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  rw [List.mem_range] at ha
  simp only [Function.comp]
  rw [bval_zc x _ _ _ (by omega) (by omega), pz_sub _ _ (by omega)]

theorem grp_fact (hm : Model x) (g : Grp) (hg : g.valid = true) :
    (g.exact = true → (g.list.map (fun i => (bval x i).toNat)).sum = 1) ∧
      1 ≤ (g.list.map (fun i => (bval x i).toNat)).sum := by
  rcases hm with ⟨_, hl, hc, _⟩
  cases g with
  | rk j qv =>
    simp only [Grp.valid, decide_eq_true_eq] at hg
    have h := hl j (by omega) (pz qv)
    rw [fsum_eq] at h
    have e1 : ((Grp.rk j qv).list.map (fun i => (bval x i).toNat)).sum = 1 := by
      rw [map_rk x j qv hg.1 hg.2.1 hg.2.2]; exact h
    exact ⟨fun _ => e1, by rw [e1]⟩
  | cov d qv =>
    simp only [Grp.valid, decide_eq_true_eq] at hg
    obtain ⟨a, ha, h1, h2⟩ := hc d hg.1 (by norm_num; exact hg.2.1) (pz qv)
    simp only [show (2:ℕ) ^ (4+1) = 32 from rfl] at ha
    refine ⟨by simp [Grp.exact], ?_⟩
    rw [map_cov x d qv hg.2.1 hg.2.2, ← fsum_eq]
    calc 1 = (x (pz qv - (a : ℤ)) a && x (pz qv - (a : ℤ)) (a + d)).toNat := by simp [h1, h2]
      _ ≤ _ := Finset.single_le_sum (f := fun (a : ℕ) => (x (pz qv - (a : ℤ)) a &&
            x (pz qv - (a : ℤ)) (a + d)).toNat) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))

end

def negAtoms : List Sat.Literal → Option (List ℕ)
  | [] => some []
  | .neg i :: r => (negAtoms r).map (i :: ·)
  | .pos _ :: _ => none

def posAtoms : List Sat.Literal → Option (List ℕ)
  | [] => some []
  | .pos i :: r => (posAtoms r).map (i :: ·)
  | .neg _ :: _ => none

theorem negAtoms_mem : ∀ (c : List Sat.Literal) (S : List ℕ), negAtoms c = some S →
    ∀ i ∈ S, List.Mem (Sat.Literal.neg i) c
  | [], S, h => by simp [negAtoms] at h; subst h; simp
  | .neg j :: r, S, h => by
    simp only [negAtoms, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact List.Mem.head _
    · exact List.Mem.tail _ (negAtoms_mem r T hT i hi)
  | .pos _ :: _, S, h => by simp [negAtoms] at h

theorem posAtoms_mem : ∀ (c : List Sat.Literal) (S : List ℕ), posAtoms c = some S →
    ∀ i ∈ S, List.Mem (Sat.Literal.pos i) c
  | [], S, h => by simp [posAtoms] at h; subst h; simp
  | .pos j :: r, S, h => by
    simp only [posAtoms, Option.map_eq_some_iff] at h
    obtain ⟨T, hT, rfl⟩ := h
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact List.Mem.head _
    · exact List.Mem.tail _ (posAtoms_mem r T hT i hi)
  | .neg _ :: _, S, h => by simp [posAtoms] at h

def cands (i : ℕ) : List Grp :=
  [.rk 1 (i / 4096 + i / 128 % 32), .rk 2 (i / 4096 + i / 128 % 32),
    .rk 3 (i / 4096 + i / 128 % 32), .rk 4 (i / 4096 + i / 128 % 32),
    .cov (i / 4 % 32 - i / 128 % 32) (i / 4096 + i / 128 % 32)]

def chkNegG (S : List ℕ) (g : Grp) : Bool :=
  g.valid && g.exact && decide (S.Nodup ∧ g.list.Nodup ∧ (∀ i ∈ S, i ∈ g.list) ∧ 1 < S.length)

def chkPosG (S : List ℕ) (g : Grp) : Bool :=
  g.valid && decide (S.Nodup ∧ g.list.Nodup ∧ (∀ i ∈ S, i ∈ g.list) ∧
    g.list.length < S.length + 1)

def chkGroup (c : List Sat.Literal) : Bool :=
  match negAtoms c with
  | some (i :: S) => (cands i).any (chkNegG (i :: S))
  | _ => match posAtoms c with
    | some (i :: S) => (cands i).any (chkPosG (i :: S))
    | _ => false

/-- dyadic parent pairs (child c, parent q) at ranks 1..4 -/
def parOK (c q : ℕ) : Bool :=
  (List.range 4).any fun j' => (List.range (2 ^ (j' + 1))).any fun a =>
    if a < 2 ^ j' then (c == a + 32 - 2 ^ (j' + 1) && q == a)
    else (c == a && q == a + 32 - 2 ^ (j' + 1))

def altOK (i j : ℕ) : Bool :=
  decide (i % 4 = 0 ∧ i / 4 % 32 = 1 ∧ (j = i + 128 ∨ i = j + 128))

def chkSmall (J : ℕ) : List Sat.Literal → Bool
  | [.pos i] => decide (i % 4 = 0 ∧ (i / 4 % 32 = 0 ∨ i / 4 % 32 = 31)) || decide (i = xc 128 J)
  | [.neg i] => decide (i = xc 128 1)
  | [.neg i, .pos j] =>
    (decide (i % 4 = 0 ∧ j % 4 = 0 ∧ i / 128 = j / 128) && parOK (i / 4 % 32) (j / 4 % 32)) ||
    decide (i % 4 = 2 ∧ (j = xc (i / 4096) (i / 128 % 32) ∨ j = xc (i / 4096) (i / 4 % 32)))
  | [.pos z, .neg i, .neg j] =>
    decide (z % 4 = 2 ∧ i = xc (z / 4096) (z / 128 % 32) ∧ j = xc (z / 4096) (z / 4 % 32))
  | [.pos i, .pos j] => altOK i j
  | [.neg i, .neg j] => altOK i j
  | _ => false

def chk (J : ℕ) (c : List Sat.Literal) : Bool := chkSmall J c || chkGroup c

theorem sat_of (v : Sat.Valuation) (c : Sat.Clause)
    (h : (∀ l, List.Mem l c → v.neg l) → False) : v.satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h (fun l hl => by cases hl)
  | cons a as ih =>
    intro ha
    exact ih (fun hall => h (fun l hl => by
      cases hl with
      | head => exact ha
      | tail _ hl => exact hall l hl))

section
variable (x : ℤ → ℕ → Bool)

theorem par_ok (hm : Model x) (p : ℤ) (c q : ℕ) (h : parOK c q = true) (hc : x p c = true) :
    x p q = true := by
  unfold parOK at h
  obtain ⟨j', hj', h⟩ := List.any_eq_true.mp h
  obtain ⟨a, ha, h⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hj' ha
  have hP := cycle_power_dyadic_tight_class_parent 5 (j' + 1) (by omega) (by omega) (x p) (hm.1 p)
    a ha
  simp only [Nat.add_sub_cancel] at hP
  split at h
  · rename_i hlt
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hP.1 hlt hc
  · rename_i hlt
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hP.2 (by omega) hc

theorem end_ok (hm : Model x) (p : ℤ) : x p 0 = true ∧ x p 31 = true := by
  have h := hm.2.1 0 (by omega) p
  simp only [pow_zero, Finset.sum_range_one, Nat.cast_zero, sub_zero, zero_add] at h
  cases h0 : x p 0 <;> cases h7 : x p 31 <;> simp_all

theorem s_small (hm : Model x) (J : ℕ) (hJ32 : J < 32) (h1 : x 0 1 = false) (hJ : x 0 J = true)
    (c : List Sat.Literal) (h : chkSmall J c = true) : (rval x).satisfies c := by
  unfold chkSmall at h
  split at h
  · rename_i i
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    apply sat_of; intro hall
    have h1 : ¬ rval x i := hall _ (List.Mem.head _)
    apply h1
    unfold rval
    rcases h with ⟨h4, h0 | h15⟩ | rfl
    · have : i = xc (i / 128) 0 := by unfold xc; omega
      rw [this, bval_xc x _ _ (by omega)]; exact (end_ok x hm _).1
    · have : i = xc (i / 128) 31 := by unfold xc; omega
      rw [this, bval_xc x _ _ (by omega)]; exact (end_ok x hm _).2
    · rw [bval_xc x _ _ hJ32]; simpa [pz] using hJ
  · rename_i i
    simp only [decide_eq_true_eq] at h
    apply sat_of; intro hall
    have h2 : rval x i := hall _ (List.Mem.head _)
    unfold rval at h2
    rw [h, bval_xc x _ _ (by omega)] at h2
    have : pz 128 = 0 := by simp [pz]
    rw [this, h1] at h2; exact absurd h2 (by simp)
  · rename_i i j
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    apply sat_of; intro hall
    have h1 : rval x i := hall _ (List.Mem.head _)
    have h2 : ¬ rval x j := hall _ (List.Mem.tail _ (List.Mem.head _))
    unfold rval at h1 h2
    apply h2
    rcases h with ⟨⟨hi, hj, hq⟩, hp⟩ | ⟨hi, hj | hj⟩
    · have ei : i = xc (i / 128) (i / 4 % 32) := by unfold xc; omega
      have ej : j = xc (i / 128) (j / 4 % 32) := by unfold xc; omega
      rw [ei, bval_xc x _ _ (by omega)] at h1
      rw [ej, bval_xc x _ _ (by omega)]
      exact par_ok x hm _ _ _ hp h1
    · have ei : i = zc (i / 4096) (i / 128 % 32) (i / 4 % 32) := by unfold zc; omega
      rw [ei, bval_zc x _ _ _ (by omega) (by omega)] at h1
      rw [hj, bval_xc x _ _ (by omega)]
      simp only [Bool.and_eq_true] at h1; exact h1.1
    · have ei : i = zc (i / 4096) (i / 128 % 32) (i / 4 % 32) := by unfold zc; omega
      rw [ei, bval_zc x _ _ _ (by omega) (by omega)] at h1
      rw [hj, bval_xc x _ _ (by omega)]
      simp only [Bool.and_eq_true] at h1; exact h1.2
  · rename_i z i j
    simp only [decide_eq_true_eq] at h
    obtain ⟨hz, hi, hj⟩ := h
    apply sat_of; intro hall
    have h0 : ¬ rval x z := hall _ (List.Mem.head _)
    have h1 : rval x i := hall _ (List.Mem.tail _ (List.Mem.head _))
    have h2 : rval x j := hall _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    unfold rval at h0 h1 h2
    apply h0
    have ez : z = zc (z / 4096) (z / 128 % 32) (z / 4 % 32) := by unfold zc; omega
    rw [hi, bval_xc x _ _ (by omega)] at h1
    rw [hj, bval_xc x _ _ (by omega)] at h2
    rw [ez, bval_zc x _ _ _ (by omega) (by omega), h1, h2]; rfl
  · rename_i i j
    simp only [altOK, decide_eq_true_eq] at h
    obtain ⟨hi, hi1, hj | hj⟩ := h
    · apply sat_of; intro hall
      have h1 : ¬ rval x i := hall _ (List.Mem.head _)
      have h2 : ¬ rval x j := hall _ (List.Mem.tail _ (List.Mem.head _))
      unfold rval at h1 h2
      have ei : i = xc (i / 128) 1 := by unfold xc; omega
      have ej : j = xc (i / 128 + 1) 1 := by unfold xc; omega
      rw [ei, bval_xc x _ _ (by omega)] at h1
      rw [ej, bval_xc x _ _ (by omega)] at h2
      have ha := hm.2.2.2 (pz (i / 128))
      have : pz (i / 128 + 1) = pz (i / 128) + 1 := by unfold pz; push_cast; ring
      rw [this, ha] at h2
      simp only [Bool.not_eq_true, Bool.not_eq_eq_eq_not] at h1 h2
      rw [h1] at h2; exact absurd h2 (by simp)
    · apply sat_of; intro hall
      have h1 : ¬ rval x i := hall _ (List.Mem.head _)
      have h2 : ¬ rval x j := hall _ (List.Mem.tail _ (List.Mem.head _))
      unfold rval at h1 h2
      have ei : i = xc (j / 128 + 1) 1 := by unfold xc; omega
      have ej : j = xc (j / 128) 1 := by unfold xc; omega
      rw [ei, bval_xc x _ _ (by omega)] at h1
      rw [ej, bval_xc x _ _ (by omega)] at h2
      have ha := hm.2.2.2 (pz (j / 128))
      have : pz (j / 128 + 1) = pz (j / 128) + 1 := by unfold pz; push_cast; ring
      rw [this, ha] at h1
      simp only [Bool.not_eq_true, Bool.not_eq_eq_eq_not] at h1 h2
      rw [h2] at h1; exact absurd h1 (by simp)
  · rename_i i j
    simp only [altOK, decide_eq_true_eq] at h
    obtain ⟨hi, hi1, hj | hj⟩ := h
    · apply sat_of; intro hall
      have h1 : rval x i := hall _ (List.Mem.head _)
      have h2 : rval x j := hall _ (List.Mem.tail _ (List.Mem.head _))
      unfold rval at h1 h2
      have ei : i = xc (i / 128) 1 := by unfold xc; omega
      have ej : j = xc (i / 128 + 1) 1 := by unfold xc; omega
      rw [ei, bval_xc x _ _ (by omega)] at h1
      rw [ej, bval_xc x _ _ (by omega)] at h2
      have ha := hm.2.2.2 (pz (i / 128))
      have : pz (i / 128 + 1) = pz (i / 128) + 1 := by unfold pz; push_cast; ring
      rw [this, ha, h1] at h2; exact absurd h2 (by simp)
    · apply sat_of; intro hall
      have h1 : rval x i := hall _ (List.Mem.head _)
      have h2 : rval x j := hall _ (List.Mem.tail _ (List.Mem.head _))
      unfold rval at h1 h2
      have ei : i = xc (j / 128 + 1) 1 := by unfold xc; omega
      have ej : j = xc (j / 128) 1 := by unfold xc; omega
      rw [ei, bval_xc x _ _ (by omega)] at h1
      rw [ej, bval_xc x _ _ (by omega)] at h2
      have ha := hm.2.2.2 (pz (j / 128))
      have : pz (j / 128 + 1) = pz (j / 128) + 1 := by unfold pz; push_cast; ring
      rw [this, ha, h2] at h1; exact absurd h1 (by simp)
  · simp at h

theorem s_group (hm : Model x) (c : List Sat.Literal) (h : chkGroup c = true) :
    (rval x).satisfies c := by
  have hf1 : ∀ i, (fun i => (bval x i).toNat) i ≤ 1 := fun i => Bool.toNat_le _
  unfold chkGroup at h
  split at h
  · rename_i i S hS
    obtain ⟨g, -, hg⟩ := List.any_eq_true.mp h
    simp only [chkNegG, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hv, hex⟩, hnd, hgnd, hsub, hlen⟩ := hg
    apply sat_of; intro hall
    have hfact := (grp_fact x hm g hv).1 hex
    refine neg_sound _ g.list (i :: S) hgnd hnd hsub 1 hfact.le hlen ?_
    intro j hj
    have := hall _ (negAtoms_mem c _ hS j hj)
    change bval x j = true at this
    simp [this]
  · split at h
    · rename_i _ i S hS
      obtain ⟨g, -, hg⟩ := List.any_eq_true.mp h
      simp only [chkPosG, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hv, hnd, hgnd, hsub, hlen⟩ := hg
      apply sat_of; intro hall
      have hfact := (grp_fact x hm g hv).2
      refine pos_sound _ hf1 g.list (i :: S) hgnd hnd hsub 1 hfact hlen ?_
      intro j hj
      have := hall _ (posAtoms_mem c _ hS j hj)
      change ¬ bval x j = true at this
      simp only [Bool.not_eq_true] at this
      simp [this]
    · simp at h

theorem s_fmla (hm : Model x) (J : ℕ) (hJ32 : J < 32) (h1 : x 0 1 = false) (hJ : x 0 J = true)
    (f : Sat.Fmla) (hf : f.all (chk J) = true) : (rval x).satisfies_fmla f :=
  ⟨fun c hc => by
    have h := List.all_eq_true.mp hf c hc
    unfold chk at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact s_small x hm J hJ32 h1 hJ c h
    · exact s_group x hm c h⟩

end

theorem model_shift (x : ℤ → ℕ → Bool) (hm : Model x) (v : ℤ) : Model (fun p a => x (v+p) a) := by
  rcases hm with ⟨hw, hl, hc, ha⟩
  refine ⟨fun p => hw (v+p), ?_, ?_, ?_⟩
  · intro j hj p
    simpa only [add_sub_assoc] using hl j hj (v+p)
  · intro d hd1 hd2 p
    obtain ⟨a, ha', h1, h2⟩ := hc d hd1 hd2 (v+p)
    exact ⟨a, ha', by simpa only [add_sub_assoc] using h1, by simpa only [add_sub_assoc] using h2⟩
  · intro p
    simpa only [add_assoc] using ha (v+p)

end RT1T32

open Lean Elab Command in
elab "rt1t32_lrat_core " nm:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  Command.liftTermElabM do
    let cnf ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat nm.getId
    addDecl <| Declaration.defnDecl {
      name := nm.getId ++ `formula, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := nm.getId ++ `sat_proof, levelParams := [], type := ← Meta.inferType proof, value := proof }

rt1t32_lrat_core RT1T32.c3 "p cnf 553323 183\n16261 16389 0\n-16133 -16261 0\n16005 16133 0\n-15877 -16005 0\n16517 16389 0\n-16901 -16773 0\n532959 536923 509175 505211 517103 521067 525031 528995 501247 513139 540887 544851 0\n536811 520955 524919 516991 532847 528883 540775 0\n529019 544875 525055 536947 540911 532983 0\n549103 553067 537211 541175 533247 545139 0\n496255 500219 504183 508147 512111 0\n512639 520567 516603 524531 528495 0\n540783 524927 532855 536819 528891 0\n536695 528767 532731 0\n-516219 -512255 0\n-532603 -528639 0\n-504187 -512115 0\n-500223 -512115 0\n-520439 -524403 0\n-512511 -524403 0\n-512511 -520439 0\n-520571 -528499 0\n-536691 -524799 0\n-532727 -524799 0\n-528763 -524799 0\n-528895 -536823 0\n-544883 -536955 0\n-545147 -541183 0\n-512099 -496243 0\n-528483 -512627 0\n-529011 -536939 0\n-521083 -536939 0\n-517119 -536939 0\n-521083 -529011 0\n-517119 -529011 0\n-545395 -553323 0\n-537467 -553323 0\n-533503 -553323 0\n-545395 -549359 0\n-537467 -549359 0\n-533503 -549359 0\n496243 -15505 -15601 0\n-496255 15505 0\n-500219 15629 0\n500223 -15629 -15741 0\n-501247 15661 0\n-504183 15753 0\n504187 -15753 -15865 0\n-505211 15785 0\n-508147 15877 0\n-509175 15989 0\n512099 -16001 -16097 0\n-512111 16109 0\n512115 -16001 -16113 0\n512255 -16005 -16125 0\n512511 -16013 -16125 0\n512627 -16017 -16113 0\n-512639 16017 0\n-513139 16033 0\n516219 -16129 -16249 0\n-516603 16249 0\n-516991 16153 0\n-517103 16157 0\n517119 -16157 -16253 0\n520439 -16261 -16373 0\n-520567 16265 0\n-520567 16373 0\n520571 -16265 -16377 0\n-520955 16277 0\n-520955 16377 0\n-521067 16281 0\n521083 -16281 -16377 0\n524403 -16385 -16497 0\n-524531 16389 0\n524799 -16397 -16509 0\n-524919 16501 0\n-524927 16401 0\n-525031 16485 0\n-525055 16405 0\n528483 -16513 -16609 0\n-528495 16621 0\n528499 -16513 -16625 0\n528639 -16517 -16637 0\n528763 -16521 -16633 0\n-528767 16521 0\n-528883 16525 0\n-528891 16525 0\n528895 -16525 -16637 0\n-528995 16609 0\n529011 -16529 -16625 0\n-529019 16529 0\n532603 -16641 -16761 0\n532727 -16645 -16757 0\n-532731 16761 0\n-532847 16649 0\n-532855 16649 0\n-532959 16733 0\n-532983 16757 0\n-533247 16661 0\n533503 -16669 -16765 0\n536691 -16769 -16881 0\n-536695 16885 0\n-536811 16873 0\n-536819 16881 0\n536823 -16773 -16885 0\n-536923 16777 0\n-536923 16857 0\n536939 -16777 -16873 0\n-536947 16881 0\n536955 -16777 -16889 0\n-537211 16785 0\n537467 -16793 -16889 0\n-540775 16997 0\n-540783 17005 0\n-540887 16901 0\n-540911 16901 0\n-541175 17013 0\n541183 -16909 -17021 0\n-544851 17105 0\n-544875 17129 0\n544883 -17025 -17137 0\n-545139 17033 0\n-545139 17137 0\n545147 -17033 -17145 0\n545395 -17041 -17137 0\n-549103 17261 0\n549359 -17165 -17261 0\n-553067 17385 0\n553323 -17289 -17385 0\n-15505 15601 0\n15741 0\n-15725 15629 0\n-15661 15725 0\n-15753 15865 0\n-15849 15753 0\n-15785 15849 0\n-15989 15877 0\n16001 0\n16125 0\n-16109 16013 0\n-16017 16113 0\n-16033 16097 0\n16129 0\n16253 0\n-16153 16249 0\n-16277 16373 0\n-16281 16377 0\n16385 0\n16509 0\n-16501 16389 0\n-16485 16389 0\n-16401 16497 0\n-16405 16501 0\n16513 0\n16637 0\n-16521 16633 0\n-16621 16525 0\n-16529 16625 0\n16641 0\n16765 0\n-16757 16645 0\n-16649 16761 0\n-16661 16757 0\n-16733 16669 0\n16769 0\n-16885 16773 0\n-16777 16889 0\n-16873 16777 0\n-16785 16881 0\n-16857 16793 0\n17021 0\n-17013 16901 0\n-16997 16901 0\n-17005 16909 0\n17025 0\n-17033 17145 0\n-17129 17033 0\n-17041 17137 0\n-17105 17041 0\n-17261 17165 0\n-17385 17289 0\n-16389 0\n16397 0\n" "183 d 0\n221 -16521 0 149 183 75 25 84 156 0\n221 d 25 84 156 0\n240 -16757 0 149 183 75 24 93 161 0\n240 d 24 93 161 0\n244 -15505 496243 0 42 130 0\n244 d 42 130 0\n245 -15753 504187 0 48 134 0\n245 d 48 134 0\n246 -17261 549359 0 127 180 0\n246 d 127 180 0\n247 -16281 521083 0 72 147 0\n247 d 72 147 0\n248 -553323 -16889 501247 505211 513139 517103 521067 528995 544851 0 155 159 160 182 1 5 151 2 83 78 3 16 4 92 137 94 51 221 85 14 102 166 6 115 37 38 112 100 170 164 107 97 7 0\n248 d 37 0\n249 -17385 553323 0 129 181 0\n249 d 129 181 0\n250 -524403 0 131 138 139 143 144 149 154 155 159 160 165 175 182 183 1 5 74 150 151 75 2 83 76 78 23 3 16 101 4 55 92 169 50 137 15 94 162 111 51 60 95 61 145 62 221 85 14 102 166 6 105 115 172 173 26 117 113 88 86 157 81 240 163 99 19 20 65 56 67 146 140 12 69 53 58 8 141 103 54 57 168 17 18 30 167 108 245 45 80 110 32 33 47 135 44 132 89 27 247 64 136 11 133 121 71 63 49 43 46 123 178 244 179 29 119 52 142 59 248 249 128 10 126 246 40 41 112 100 170 164 107 97 7 0\n250 d 19 20 67 110 32 33 27 121 123 0\n259 -16873 536939 0 108 168 0\n259 d 108 168 0\n260 -17033 0 148 149 155 159 165 171 182 183 5 75 83 23 16 101 92 104 94 162 96 221 85 14 102 166 105 26 88 87 250 73 152 77 13 114 174 118 28 124 176 0\n260 d 104 96 87 73 152 77 13 114 174 118 28 124 176 0\n318 -17041 545395 0 125 178 0\n318 d 125 178 0\n319 -549359 0 131 138 139 143 144 149 154 155 159 160 165 182 183 1 5 74 150 151 75 2 83 76 153 78 23 3 16 79 101 4 55 92 109 50 137 15 94 162 51 60 95 61 145 62 221 85 14 102 166 6 105 115 116 173 26 113 88 86 157 81 240 98 260 177 120 9 91 158 82 90 22 31 34 35 259 247 64 103 71 63 8 69 70 146 68 65 66 21 12 56 58 140 141 53 54 57 17 18 30 245 45 80 47 135 44 132 89 136 11 133 49 43 46 244 29 52 142 59 39 318 179 119 40 41 100 164 97 7 106 167 107 112 170 0\n319 d 39 40 41 107 112 170 0\n340 0 131 138 139 143 144 149 154 155 159 160 165 182 183 1 5 74 150 151 75 2 83 76 153 78 23 3 16 79 101 4 55 92 109 169 50 137 15 94 162 111 51 60 95 61 145 62 221 85 14 102 166 6 105 115 116 172 173 26 117 113 88 86 157 81 240 98 163 99 260 122 177 120 9 91 158 82 90 22 31 34 35 259 247 64 103 71 63 8 69 70 146 68 65 66 21 12 56 58 140 141 53 54 57 17 18 30 245 45 80 47 135 44 132 89 136 11 133 49 43 46 244 29 52 142 59 319 246 126 10 128 249 36 38 318 100 179 164 119 97 248 7 167 106 0\n"


theorem rt1t32_refute_3 (x : ℤ → ℕ → Bool) (hm : RT1T32.Model x) (h1 : x 0 1 = false)
    (hJ : x 0 3 = true) : False := by
  have hF : (RT1T32.rval x).satisfies_fmla RT1T32.c3.formula :=
    RT1T32.s_fmla x hm 3 (by norm_num) h1 hJ _ (by decide +kernel)
  exact RT1T32.c3.sat_proof _ hF

rt1t32_lrat_core RT1T32.c7 "p cnf 581831 396\n16261 16389 0\n16517 16389 0\n-16645 -16517 0\n16773 16645 0\n-16901 -16773 0\n17029 16901 0\n-17157 -17029 0\n17285 17157 0\n-17413 -17285 0\n573775 538099 534135 526207 542063 546027 549991 553955 557919 569811 565847 561883 530171 577739 581703 0\n517487 521451 529379 545235 505595 513523 525415 509559 533343 537307 541271 553163 549199 501631 557127 0\n521467 529395 525431 545251 533359 537323 541287 549215 517503 553179 557143 0\n553183 541291 525435 521471 537327 533363 545255 549219 529399 557147 0\n537459 561243 533495 525567 541423 545387 549351 553315 557279 529531 0\n557151 525439 533367 537331 529403 545259 549223 553187 541295 0\n545135 553063 533243 537207 529279 549099 541171 0\n565487 569451 557559 549631 553595 561523 0\n561787 569715 557823 577643 573679 565751 0\n529019 536947 532983 525055 540911 544875 0\n545139 553067 541175 533247 549103 537211 0\n561259 545403 549367 541439 557295 553331 0\n553071 545143 537215 549107 541179 0\n541311 545275 549239 557167 553203 0\n545151 553079 549115 0\n-524411 -520447 0\n-557179 -553215 0\n-520571 -528499 0\n-516607 -528499 0\n-565363 -553471 0\n-561399 -553471 0\n-569459 -561531 0\n-565495 -561531 0\n-557567 -561531 0\n-536955 -544883 0\n-553075 -545147 0\n-541183 -553075 0\n-541183 -545147 0\n-549243 -553207 0\n-553207 -545279 0\n-549243 -545279 0\n-553339 -561267 0\n-549375 -561267 0\n-520555 -528483 0\n-516591 -528483 0\n-569707 -553851 0\n-569707 -549887 0\n-565743 -553851 0\n-549887 -565743 0\n-553851 -561779 0\n-577899 -562043 0\n-577899 -558079 0\n-573935 -562043 0\n-573935 -558079 0\n-569971 -562043 0\n-569971 -558079 0\n-562043 -558079 0\n-544867 -529011 0\n-553059 -525311 0\n-545131 -525311 0\n-537203 -525311 0\n-529275 -525311 0\n-553191 -541299 0\n-553191 -537335 0\n-553191 -533371 0\n-553191 -529407 0\n-545263 -537335 0\n-545263 -533371 0\n-529407 -545263 0\n-541299 -537335 0\n-541299 -533371 0\n-541299 -529407 0\n-553323 -545395 0\n-553323 -537467 0\n-545395 -537467 0\n-538095 -553951 0\n-530167 -553951 0\n-581831 -562011 0\n-581831 -558047 0\n-577867 -562011 0\n-577867 -558047 0\n-573903 -562011 0\n-573903 -558047 0\n-525411 -521447 0\n-525411 -517483 0\n-513519 -525411 0\n-509555 -525411 0\n-505591 -525411 0\n-501627 -525411 0\n-513519 -521447 0\n-509555 -521447 0\n-505591 -521447 0\n-501627 -521447 0\n-513519 -517483 0\n-509555 -517483 0\n-505591 -517483 0\n-501627 -517483 0\n-553291 -529507 0\n-549327 -529507 0\n-545363 -529507 0\n501627 -15673 -15737 0\n-501631 15673 0\n505591 -15797 -15861 0\n-505595 15797 0\n509555 -15921 -15985 0\n-509559 15921 0\n513519 -16045 -16109 0\n-513523 16045 0\n516591 -16141 -16237 0\n516607 -16141 -16253 0\n517483 -16169 -16233 0\n-517487 16237 0\n-517503 16169 0\n520447 -16261 -16381 0\n520555 -16265 -16361 0\n520571 -16265 -16377 0\n521447 -16293 -16357 0\n-521451 16293 0\n-521451 16361 0\n-521467 16293 0\n-521471 16293 0\n524411 -16385 -16505 0\n-525055 16405 0\n525311 -16413 -16509 0\n525411 -16417 -16481 0\n-525415 16485 0\n-525431 16501 0\n-525435 16505 0\n-525439 16417 0\n-525567 16421 0\n-526207 16441 0\n528483 -16513 -16609 0\n528499 -16513 -16625 0\n529011 -16529 -16625 0\n-529019 16529 0\n529275 -16537 -16633 0\n-529279 16537 0\n-529379 16541 0\n-529395 16541 0\n-529399 16541 0\n-529403 16541 0\n529407 -16541 -16637 0\n529507 -16545 -16609 0\n-529531 16545 0\n530167 -16565 -16629 0\n-530171 16565 0\n-532983 16757 0\n-533243 16661 0\n-533247 16661 0\n-533343 16665 0\n-533359 16665 0\n-533363 16665 0\n-533367 16757 0\n533371 -16665 -16761 0\n-533495 16757 0\n-534135 16757 0\n-536947 16777 0\n536955 -16777 -16889 0\n537203 -16785 -16881 0\n-537207 16785 0\n-537211 16785 0\n-537215 16785 0\n-537307 16789 0\n-537323 16789 0\n-537327 16789 0\n-537331 16789 0\n537335 -16789 -16885 0\n-537459 16793 0\n537467 -16793 -16889 0\n538095 -16813 -16877 0\n-538099 16813 0\n-540911 16901 0\n-541171 16909 0\n-541175 17013 0\n-541179 16909 0\n541183 -16909 -17021 0\n-541271 16981 0\n-541287 16997 0\n-541291 16913 0\n-541295 17005 0\n541299 -16913 -17009 0\n-541311 16913 0\n-541423 16917 0\n-541439 16917 0\n-542063 17005 0\n544867 -17025 -17121 0\n-544875 17129 0\n544883 -17025 -17137 0\n545131 -17033 -17129 0\n-545135 17033 0\n-545135 17133 0\n-545139 17033 0\n-545139 17137 0\n-545143 17033 0\n545147 -17033 -17145 0\n-545151 17033 0\n-545235 17105 0\n-545251 17037 0\n-545251 17121 0\n-545255 17037 0\n-545259 17129 0\n545263 -17037 -17133 0\n-545275 17037 0\n545279 -17037 -17149 0\n545363 -17041 -17105 0\n-545387 17129 0\n545395 -17041 -17137 0\n-545403 17041 0\n-546027 17129 0\n-549099 17157 0\n-549103 17157 0\n-549107 17157 0\n-549115 17157 0\n-549199 17161 0\n-549199 17229 0\n-549215 17161 0\n-549215 17245 0\n-549219 17161 0\n-549223 17253 0\n-549239 17269 0\n549243 -17161 -17273 0\n549327 -17165 -17229 0\n-549351 17253 0\n-549367 17269 0\n549375 -17165 -17277 0\n-549631 17173 0\n549887 -17181 -17277 0\n-549991 17253 0\n553059 -17281 -17377 0\n-553063 17381 0\n-553067 17385 0\n-553071 17389 0\n553075 -17281 -17393 0\n-553079 17397 0\n-553163 17353 0\n-553179 17369 0\n-553183 17373 0\n-553187 17377 0\n553191 -17285 -17381 0\n-553203 17393 0\n553207 -17285 -17397 0\n553215 -17285 -17405 0\n553291 -17289 -17353 0\n-553315 17377 0\n553323 -17289 -17385 0\n-553331 17393 0\n553339 -17289 -17401 0\n553471 -17293 -17405 0\n-553595 17297 0\n553851 -17305 -17401 0\n553951 -17309 -17373 0\n-553955 17377 0\n-557127 17477 0\n-557143 17493 0\n-557147 17497 0\n-557151 17501 0\n-557167 17517 0\n557179 -17409 -17529 0\n-557279 17413 0\n-557295 17413 0\n-557559 17525 0\n557567 -17421 -17533 0\n-557823 17429 0\n-557919 17433 0\n558047 -17437 -17501 0\n558079 -17437 -17533 0\n-561243 17625 0\n-561259 17641 0\n561267 -17537 -17649 0\n561399 -17541 -17653 0\n-561523 17545 0\n-561523 17649 0\n561531 -17545 -17657 0\n561779 -17553 -17649 0\n-561787 17553 0\n-561883 17557 0\n562011 -17561 -17625 0\n562043 -17561 -17657 0\n565363 -17665 -17777 0\n-565487 17773 0\n565495 -17669 -17781 0\n565743 -17677 -17773 0\n-565751 17781 0\n-565847 17681 0\n-569451 17897 0\n569459 -17793 -17905 0\n569707 -17801 -17897 0\n-569715 17905 0\n-569811 17873 0\n569971 -17809 -17905 0\n-573679 18029 0\n-573775 17997 0\n573903 -17933 -17997 0\n573935 -17933 -18029 0\n-577643 18153 0\n-577739 18121 0\n577867 -18057 -18121 0\n577899 -18057 -18153 0\n-581703 18245 0\n581831 -18181 -18245 0\n-15673 15737 0\n-15797 15861 0\n-15921 15985 0\n-16045 16109 0\n16253 0\n-16237 16141 0\n-16169 16233 0\n16381 0\n-16265 16377 0\n-16361 16265 0\n-16293 16357 0\n16385 0\n16509 0\n-16501 16389 0\n-16485 16389 0\n-16405 16501 0\n-16417 16481 0\n-16421 16485 0\n-16441 16505 0\n16513 0\n16637 0\n-16529 16625 0\n-16537 16633 0\n-16545 16609 0\n-16565 16629 0\n-16757 16645 0\n-16661 16757 0\n-16665 16761 0\n-16777 16889 0\n-16785 16881 0\n-16789 16885 0\n-16793 16889 0\n-16813 16877 0\n17021 0\n-17013 16901 0\n-16997 16901 0\n-17005 16909 0\n-16913 17009 0\n-16917 17013 0\n-16981 16917 0\n17025 0\n17149 0\n-17033 17145 0\n-17129 17033 0\n-17133 17037 0\n-17041 17137 0\n-17105 17041 0\n17277 0\n-17269 17157 0\n-17161 17273 0\n-17253 17157 0\n-17173 17269 0\n-17229 17165 0\n-17245 17181 0\n17281 0\n17405 0\n-17289 17401 0\n-17385 17289 0\n-17389 17293 0\n-17297 17393 0\n-17305 17401 0\n-17353 17289 0\n-17369 17305 0\n-17373 17309 0\n17409 0\n17533 0\n-17525 17413 0\n-17517 17421 0\n-17429 17525 0\n-17433 17529 0\n-17477 17413 0\n-17493 17429 0\n-17497 17433 0\n-17501 17437 0\n17537 0\n-17653 17541 0\n-17545 17657 0\n-17641 17545 0\n-17553 17649 0\n-17557 17653 0\n-17561 17657 0\n-17625 17561 0\n17665 0\n-17781 17669 0\n-17773 17677 0\n-17681 17777 0\n17793 0\n-17897 17801 0\n-17809 17905 0\n-17873 17809 0\n-18029 17933 0\n-17997 17933 0\n-18153 18057 0\n-18121 18057 0\n-18245 18181 0\n-16389 0\n16413 0\n" "396 d 42 224 0\n397 -17033 545147 0 194 342 0\n397 d 194 342 0\n398 -16785 0 312 396 123 60 329 158 0\n398 d 60 329 158 0\n399 -17041 545395 0 345 206 0\n399 d 206 0\n400 -16537 0 312 396 123 61 322 135 0\n400 d 61 322 135 0\n401 -16913 541299 0 180 337 0\n401 d 180 337 0\n402 -16293 521447 0 116 310 0\n402 d 116 310 0\n403 -16665 533371 0 153 327 0\n403 d 153 327 0\n404 -16789 537335 0 166 330 0\n404 d 166 330 0\n405 -17161 549243 0 220 349 0\n405 d 220 349 0\n406 -16417 525411 0 124 316 0\n406 d 124 316 0\n407 -16565 530167 0 144 324 0\n407 d 144 324 0\n408 -16813 538095 0 169 332 0\n408 d 169 332 0\n409 16909 521471 533363 537327 541291 545135 545143 545255 546027 549219 565847 569811 573775 577739 581703 0 307 311 312 320 354 355 364 395 396 1 2 123 113 3 58 25 4 325 228 121 5 155 326 251 127 318 6 147 130 7 8 209 211 350 241 227 26 257 369 263 372 254 398 159 161 400 136 172 174 336 16 22 184 229 231 238 358 65 247 141 30 139 13 236 363 250 75 76 408 407 170 145 10 275 379 269 375 0\n409 d 1 113 25 121 155 251 127 318 130 241 227 26 257 369 263 372 254 184 30 139 13 236 363 250 75 76 408 407 170 145 10 275 379 269 375 0\n410 -17545 561531 0 376 272 0\n410 d 272 0\n411 16909 521471 533363 537327 541291 545135 545143 545255 546027 549219 569811 573775 577739 581703 0 355 382 395 2 3 4 5 6 7 211 398 161 409 174 283 22 385 231 278 358 29 247 0\n411 d 211 161 409 174 283 22 385 231 278 358 29 247 0\n412 17393 541311 545275 545403 0 365 395 2 3 4 5 6 334 7 338 8 348 183 9 219 223 259 239 245 23 21 256 267 367 377 261 410 33 0\n414 -17501 558047 0 264 373 0\n414 d 264 0\n415 -17773 565743 0 281 384 0\n415 d 281 384 0\n416 -16169 517483 0 110 306 0\n416 d 110 306 0\n417 -15673 501627 0 100 300 0\n417 d 100 300 0\n418 -15797 505591 0 102 301 0\n418 d 102 301 0\n419 -15921 509555 0 104 302 0\n419 d 104 302 0\n420 -16045 513519 0 106 303 0\n420 d 106 303 0\n421 -16793 537467 0 331 168 0\n421 d 331 168 0\n422 -16777 536955 0 157 328 0\n422 d 157 328 0\n423 -16545 529507 0 142 323 0\n423 d 142 0\n424 -17625 562011 0 381 276 0\n424 d 276 0\n425 -581831 -17289 529379 529403 533343 537307 537331 537459 541295 545235 545259 545387 549199 0 312 319 354 395 396 2 314 123 3 125 317 58 4 325 129 228 5 152 154 237 243 6 334 7 338 8 350 182 339 9 218 222 176 258 370 252 77 78 424 414 266 255 14 15 143 128 423 323 406 97 131 83 85 86 87 88 242 44 402 420 419 418 417 234 117 107 105 103 101 11 111 305 108 0\n425 d 77 78 0\n426 -18245 581831 0 299 394 0\n426 d 299 394 0\n427 -16545 -17289 501631 505595 509559 513523 521451 529379 533343 537307 545235 549199 0 319 395 2 314 3 125 4 5 6 334 7 338 8 339 9 176 370 252 423 323 131 97 44 242 234 11 111 305 108 0\n427 d 97 44 242 108 0\n428 -569971 -17289 529379 529403 533343 537307 537331 537459 541295 545235 545259 545387 549199 0 312 354 365 395 396 2 314 123 3 317 58 4 325 129 228 5 152 154 237 243 6 334 7 338 8 350 182 9 218 222 258 54 55 265 373 255 15 128 406 83 85 86 87 88 402 420 419 418 417 117 107 105 103 101 427 143 14 266 381 380 277 0\n428 d 54 55 0\n429 -17809 569971 0 289 388 0\n429 d 289 388 0\n430 -577867 -17289 529379 529403 533343 537307 537331 537459 541295 545235 545259 545387 549199 0 312 354 395 396 2 314 123 3 317 58 4 325 129 228 5 152 154 237 243 6 334 7 338 8 350 182 9 218 222 258 79 80 424 414 266 255 14 15 143 128 406 83 85 86 87 88 402 420 419 418 417 117 107 105 103 101 427 0\n430 d 79 80 0\n431 -18121 577867 0 296 393 0\n431 d 296 393 0\n432 -573903 -17289 529379 529403 533343 537307 537331 537459 541295 545235 545259 545387 549199 0 312 354 395 396 2 314 123 3 317 58 4 325 129 228 5 152 154 237 243 6 334 7 338 8 350 182 9 218 222 258 81 82 424 414 266 255 14 15 143 128 406 83 85 86 87 88 402 420 419 418 417 117 107 105 103 101 427 0\n432 d 81 82 424 414 117 0\n433 -17997 573903 0 292 391 0\n433 d 292 391 0\n436 -17561 562043 0 277 380 0\n436 d 380 0\n437 16909 -17289 537459 545135 545143 545235 545255 545259 545387 546027 549199 549219 0 312 319 320 354 365 395 396 2 314 123 3 317 58 4 325 129 228 5 152 154 326 237 243 6 334 147 7 338 8 209 350 182 9 218 222 258 398 159 400 136 172 336 16 179 229 238 62 63 64 65 401 404 403 141 162 165 149 137 140 432 428 425 430 178 164 151 433 429 426 431 291 389 298 295 288 411 120 402 83 89 90 91 92 406 420 419 418 417 128 107 105 103 101 15 255 373 265 56 436 381 266 14 143 323 427 131 118 43 309 114 0\n437 d 432 428 425 430 178 164 151 433 429 426 431 291 389 298 295 288 411 120 0\n438 -553851 553595 561523 0 395 2 3 4 5 6 7 8 348 9 351 366 225 260 45 47 415 279 17 284 286 387 0\n438 d 45 47 0\n439 -17781 565495 0 280 383 0\n439 d 280 383 0\n440 -18029 573935 0 293 390 0\n440 d 293 390 0\n441 -18153 577899 0 297 392 0\n441 d 297 392 0\n442 -16361 520555 0 309 114 0\n442 d 114 0\n443 -521447 -16545 -17289 529379 533343 537307 545235 549199 0 319 89 90 91 92 323 420 419 418 417 131 107 105 103 101 43 427 442 118 0\n444 -16545 -17289 529379 529395 533343 533359 537307 537323 545235 545251 549199 549215 553179 0 319 395 2 313 3 126 4 5 6 335 7 177 8 9 366 368 371 253 323 131 43 442 118 443 402 119 12 112 416 93 94 95 96 420 419 418 417 107 105 103 101 427 0\n444 d 443 0\n445 17033 0 312 320 333 341 354 374 386 395 396 2 314 123 3 317 58 4 325 129 228 5 154 326 243 6 334 148 7 173 338 8 210 212 348 350 182 183 9 223 222 258 259 366 368 262 398 160 343 195 193 191 189 200 205 208 24 20 233 230 240 357 244 38 39 356 246 72 73 405 203 41 399 421 213 215 217 197 199 202 268 207 346 167 378 271 196 274 437 175 36 232 245 359 412 21 248 181 267 438 401 377 249 71 70 69 410 376 362 141 403 404 32 31 235 137 138 149 150 162 163 439 285 444 282 287 143 14 266 381 277 50 52 441 440 294 290 18 0\n445 d 212 343 195 193 191 189 208 24 233 240 38 39 72 217 199 437 36 71 70 69 376 277 0\n446 -17105 545363 0 346 204 0\n446 d 204 0\n447 -525411 517487 521451 529379 529395 533343 533359 537307 537323 545235 545251 549199 549215 0 354 374 395 2 313 314 3 126 125 4 5 6 334 335 7 338 177 8 339 9 176 366 370 368 252 371 253 445 397 35 232 359 248 83 84 85 86 87 88 402 416 420 419 418 417 119 112 107 105 103 101 12 11 235 234 362 361 360 246 249 41 438 268 271 0\n447 d 271 0\n448 -17553 561779 0 378 273 0\n448 d 273 0\n450 -17305 553851 0 360 249 0\n450 d 360 249 0\n451 -521447 517487 521451 529379 533343 537307 545235 549199 553163 0 395 2 314 3 125 4 5 6 334 7 338 8 339 9 176 370 252 89 420 107 90 419 105 91 418 103 11 101 417 92 0\n451 d 89 90 91 92 0\n452 17545 517487 521451 529379 529395 533343 533359 537307 537323 545235 545251 549199 549215 561243 0 312 354 395 396 2 313 314 123 3 126 125 317 58 59 4 325 129 228 5 154 243 6 334 335 7 338 177 8 348 350 182 183 339 9 223 222 176 258 259 366 370 368 252 371 253 445 188 397 205 35 232 245 359 248 270 377 438 267 450 21 362 207 235 399 74 421 167 14 143 444 361 234 451 402 119 12 112 416 93 94 95 96 420 419 418 417 107 105 103 101 11 0\n452 d 444 0\n453 545235 517487 521451 529379 529395 529403 533343 533359 537307 537323 537331 545251 549199 549215 561787 0 312 333 354 365 386 395 396 2 123 3 58 59 4 325 228 5 152 237 6 7 8 350 9 218 366 368 262 445 188 397 200 37 175 336 179 447 406 128 15 255 373 265 51 53 56 441 440 436 294 290 381 266 452 410 32 31 439 285 282 287 18 0\n453 d 447 452 0\n454 -562043 529395 529403 533359 537323 537331 545251 549215 561787 0 312 333 354 365 386 395 396 2 313 123 3 126 58 59 4 325 228 5 152 237 6 335 7 177 8 350 9 218 366 368 262 371 253 445 188 397 200 35 37 232 175 359 336 248 179 50 52 56 441 440 265 294 290 373 255 15 128 406 83 84 402 416 119 112 12 235 362 450 438 270 410 32 31 439 285 282 287 18 0\n455 -17105 561243 0 312 354 395 396 2 314 123 3 317 58 59 4 325 129 228 5 154 243 6 334 7 338 8 350 182 9 222 258 445 188 205 446 346 99 399 423 74 143 421 14 167 0\n455 d 446 99 0\n456 -16265 520571 0 115 308 0\n456 d 115 308 0\n457 561787 517487 521451 529379 529395 529403 533343 533359 537307 537323 537331 545251 549199 549215 0 454 436 381 266 455 196 453 0\n457 d 454 453 0\n458 -525411 529395 533359 537323 545251 549215 553179 0 395 2 313 3 126 4 5 6 335 7 177 8 9 366 368 371 253 83 402 119 12 112 416 84 0\n458 d 83 84 0\n459 553163 517487 521451 529379 529395 533343 533359 537307 537323 545235 545251 549199 549215 553179 0 395 2 313 314 3 126 125 4 5 6 334 335 7 338 177 8 339 9 176 366 370 368 252 371 253 451 402 119 12 112 416 93 420 107 94 419 105 95 418 103 96 417 101 11 0\n459 d 126 125 335 177 339 176 370 252 371 253 451 402 119 12 112 416 93 94 95 96 11 0\n460 -553191 517487 521451 545251 549199 549215 0 312 320 333 354 365 374 395 396 2 123 3 58 59 4 325 228 5 152 237 6 7 350 218 445 188 397 200 37 175 336 179 63 64 65 404 403 141 162 163 165 149 150 137 138 140 457 274 448 378 49 268 450 41 362 235 458 406 128 15 255 373 265 56 436 381 266 455 196 459 234 361 356 246 0\n461 549199 517487 521451 545251 549215 0 312 320 333 354 365 374 395 396 2 123 3 58 59 4 325 228 5 152 326 237 6 147 7 8 209 350 218 398 159 400 136 445 188 397 200 37 175 172 336 179 460 238 229 16 190 344 201 66 68 67 404 141 403 162 163 165 137 138 140 149 150 457 274 378 268 41 448 49 450 362 235 458 406 128 15 255 373 265 56 436 381 266 455 196 459 234 361 356 246 0\n461 d 457 448 49 455 459 234 361 0\n462 17037 557167 0 333 354 395 2 3 4 325 5 326 6 147 7 8 209 348 219 398 159 400 136 445 397 35 37 232 175 239 172 202 344 190 16 229 238 62 401 181 23 0\n462 d 219 239 23 0\n463 -16529 549199 549215 0 304 319 340 321 132 27 28 456 109 309 305 118 111 133 461 57 198 185 0\n463 d 133 461 57 198 185 0\n464 -562043 561787 565751 569715 0 395 2 3 4 5 6 7 8 9 366 368 262 50 441 294 18 290 440 52 0\n464 d 50 52 0\n465 -545263 -16545 -17289 545235 549199 557151 0 312 319 320 333 354 395 396 2 123 3 58 59 4 325 228 5 152 237 6 7 350 218 445 188 397 200 37 175 336 179 323 131 43 442 118 66 404 162 165 68 141 137 140 15 128 406 85 86 87 88 420 419 418 417 107 105 103 101 427 149 403 67 0\n465 d 66 68 67 0\n466 557151 -17037 0 312 319 320 333 340 341 354 374 386 395 396 2 313 314 123 3 315 317 58 59 4 325 122 129 228 5 146 152 154 326 237 243 6 171 334 147 148 7 173 338 8 209 210 348 350 182 183 9 223 218 222 258 259 398 159 160 400 136 445 188 397 186 200 205 35 37 232 175 245 172 336 179 203 40 405 213 215 463 134 19 156 422 34 187 345 192 207 20 21 230 267 357 377 356 410 246 32 31 41 439 285 268 282 287 378 274 346 244 464 436 381 266 196 73 421 167 14 143 465 323 201 190 16 229 238 63 64 65 404 403 141 165 140 15 128 406 131 162 149 137 85 86 87 88 43 420 419 418 417 442 118 107 105 103 101 427 0\n466 d 346 244 464 196 73 465 323 201 131 162 149 137 85 86 87 88 43 420 419 418 417 442 107 105 103 101 427 0\n467 -17037 0 312 340 341 354 365 374 386 395 396 2 313 123 3 315 59 4 325 122 5 146 326 6 171 334 148 7 173 338 8 210 348 183 9 223 259 366 368 262 398 160 445 188 397 186 35 232 245 203 466 255 373 265 40 51 53 405 441 440 213 215 294 290 463 134 19 156 422 34 187 345 207 192 21 20 267 230 377 410 357 32 31 356 439 285 246 282 287 41 18 268 274 378 0\n467 d 148 173 210 183 223 259 368 262 160 245 203 466 40 51 53 405 441 440 213 215 294 290 463 192 21 20 267 230 377 357 32 31 356 439 285 246 282 287 41 18 268 274 378 0\n468 549215 0 304 312 319 320 333 340 354 365 395 396 2 313 314 123 3 315 317 58 59 4 325 122 129 228 5 146 152 154 326 237 243 6 171 334 147 7 338 8 209 350 182 9 218 222 258 398 159 400 136 445 188 397 186 200 205 35 37 232 175 359 172 336 248 179 467 197 202 344 462 190 256 16 367 229 261 238 33 62 63 64 65 410 401 404 403 141 270 181 163 165 150 138 140 438 412 450 207 362 399 345 235 74 187 421 34 167 422 156 19 134 321 132 27 28 456 109 309 305 118 111 460 458 214 406 352 128 221 15 98 255 423 373 143 265 14 56 266 436 381 0\n468 d 313 314 123 315 317 58 59 325 122 129 228 146 152 154 326 237 243 171 334 147 338 209 350 182 218 222 258 159 136 188 186 200 205 37 175 172 336 179 197 202 344 190 16 229 238 62 63 64 65 401 404 403 141 181 163 165 150 138 140 438 412 450 207 362 399 345 235 74 187 421 34 167 422 156 19 134 321 132 27 28 456 109 309 305 118 111 460 458 214 406 352 128 221 15 98 255 423 373 143 265 14 56 266 436 381 0\n470 0 347 354 365 395 2 3 4 5 6 7 8 348 9 351 366 225 260 445 397 35 232 359 248 467 462 256 367 261 33 410 270 468 216 353 226 46 48 415 279 17 284 286 387 0\n"


theorem rt1t32_refute_7 (x : ℤ → ℕ → Bool) (hm : RT1T32.Model x) (h1 : x 0 1 = false)
    (hJ : x 0 7 = true) : False := by
  have hF : (RT1T32.rval x).satisfies_fmla RT1T32.c7.formula :=
    RT1T32.s_fmla x hm 7 (by norm_num) h1 hJ _ (by decide +kernel)
  exact RT1T32.c7.sat_proof _ hF

rt1t32_lrat_core RT1T32.c24 "p cnf 581831 636\n16261 16389 0\n-16133 -16261 0\n16005 16133 0\n-15877 -16005 0\n15749 15877 0\n-15621 -15749 0\n15493 15621 0\n-15365 -15493 0\n16517 16389 0\n-16645 -16517 0\n16773 16645 0\n-16901 -16773 0\n17029 16901 0\n-17157 -17029 0\n17285 17157 0\n-17413 -17285 0\n480755 520395 512467 516431 484719 488683 492647 496611 500575 504539 508503 472827 468863 476791 524359 0\n561883 565847 534135 526207 530171 553955 549991 581703 557919 538099 542063 569811 573775 577739 546027 0\n501631 545235 509559 513523 517487 521451 525415 537307 533343 505595 541271 549199 553163 529379 557127 0\n537971 569683 534007 526079 541935 577611 549863 573647 557791 545899 553827 530043 561755 565719 0\n488699 484735 492663 496627 500591 504555 508519 512483 520411 516447 524375 0\n549215 553179 525431 521467 517503 537323 541287 533359 545251 529395 557143 0\n504691 496763 500727 492799 508655 528475 516583 520547 524511 512619 0\n553183 545255 525435 521471 549219 533363 529399 537327 541291 557147 0\n561243 553315 533495 525567 541423 537459 549351 545387 557279 529531 0\n520419 524383 496635 500599 508527 504563 516455 512491 492671 0\n525439 557151 533367 537331 541295 545259 549223 529403 553187 0\n504439 496511 500475 508403 512367 516331 520295 0\n512499 516463 508535 504571 500607 520427 524391 0\n553063 537207 533243 545135 529279 549099 541171 0\n512635 528491 516599 508671 524527 520563 0\n569451 561523 557559 549631 553595 565487 0\n577643 569715 557823 561787 573679 565751 0\n536683 528755 524791 516863 532719 520827 0\n536947 529019 532983 525055 540911 544875 0\n553067 537211 541175 533247 549103 545139 0\n561259 553331 549367 541439 557295 545403 0\n504183 500219 496255 508147 512111 0\n553071 541179 545143 549107 537215 0\n557167 553203 549239 541311 545275 0\n520311 512383 516347 0\n553079 545151 549115 0\n-524411 -520447 0\n-557179 -553215 0\n-520307 -512379 0\n-508415 -520307 0\n-508415 -512379 0\n-504187 -512115 0\n-500223 -512115 0\n-516475 -520439 0\n-512511 -520439 0\n-528499 -520571 0\n-516607 -528499 0\n-565363 -553471 0\n-561399 -553471 0\n-569459 -561531 0\n-565495 -561531 0\n-561531 -557567 0\n-528763 -536691 0\n-544883 -536955 0\n-532991 -536955 0\n-545147 -553075 0\n-541183 -553075 0\n-541183 -545147 0\n-549243 -553207 0\n-545279 -553207 0\n-561267 -553339 0\n-549375 -561267 0\n-520291 -504435 0\n-520291 -496507 0\n-504435 -512363 0\n-496507 -512363 0\n-496243 -512099 0\n-520423 -524387 0\n-516459 -524387 0\n-512495 -524387 0\n-508531 -524387 0\n-504567 -524387 0\n-500603 -524387 0\n-496639 -524387 0\n-520555 -528483 0\n-512627 -528483 0\n-520555 -512627 0\n-504699 -520555 0\n-504699 -512627 0\n-569707 -553851 0\n-569707 -549887 0\n-565743 -553851 0\n-565743 -549887 0\n-553851 -561779 0\n-549887 -561779 0\n-577899 -562043 0\n-577899 -558079 0\n-573935 -562043 0\n-573935 -558079 0\n-569971 -562043 0\n-558079 -569971 0\n-566007 -562043 0\n-544867 -536939 0\n-544867 -529011 0\n-529011 -536939 0\n-521083 -536939 0\n-517119 -536939 0\n-532975 -529011 0\n-521083 -529011 0\n-517119 -529011 0\n-553059 -529275 0\n-553059 -525311 0\n-529275 -545131 0\n-545131 -525311 0\n-529275 -537203 0\n-537203 -525311 0\n-529275 -525311 0\n-541299 -553191 0\n-537335 -553191 0\n-533371 -553191 0\n-529407 -553191 0\n-537335 -545263 0\n-533371 -545263 0\n-529407 -545263 0\n-541299 -529407 0\n-545395 -553323 0\n-537467 -553323 0\n-488679 -492643 0\n-484715 -492643 0\n-480751 -492643 0\n-476787 -492643 0\n-472823 -492643 0\n-468859 -492643 0\n-496739 -520523 0\n-496739 -512595 0\n-538095 -553951 0\n-530167 -553951 0\n-581831 -562011 0\n-581831 -558047 0\n-577867 -562011 0\n-577867 -558047 0\n-573903 -562011 0\n-573903 -558047 0\n-505591 -525411 0\n-501627 -525411 0\n-529507 -553291 0\n-529507 -545363 0\n468859 -14649 -14713 0\n-468863 14649 0\n472823 -14773 -14837 0\n-472827 14773 0\n476787 -14897 -14961 0\n-476791 14897 0\n480751 -15021 -15085 0\n-480755 15021 0\n484715 -15145 -15209 0\n-484719 15145 0\n-484735 15145 0\n488679 -15269 -15333 0\n-488683 15269 0\n-488699 15269 0\n492643 -15393 -15457 0\n-492647 15461 0\n-492663 15477 0\n-492671 15393 0\n-492799 15397 0\n496243 -15505 -15601 0\n-496255 15505 0\n496507 -15513 -15609 0\n-496511 15513 0\n-496611 15517 0\n-496627 15517 0\n-496635 15517 0\n496639 -15517 -15613 0\n496739 -15521 -15585 0\n-496763 15521 0\n-500219 15629 0\n500223 -15629 -15741 0\n-500475 15637 0\n-500575 15641 0\n-500591 15641 0\n-500599 15733 0\n500603 -15641 -15737 0\n-500607 15641 0\n-500727 15733 0\n501627 -15673 -15737 0\n-501631 15673 0\n-504183 15753 0\n504187 -15753 -15865 0\n504435 -15761 -15857 0\n-504439 15761 0\n-504539 15765 0\n-504555 15765 0\n-504563 15765 0\n504567 -15765 -15861 0\n-504571 15765 0\n-504691 15769 0\n504699 -15769 -15865 0\n505591 -15797 -15861 0\n-505595 15797 0\n-508147 15877 0\n-508403 15885 0\n508415 -15885 -15997 0\n-508503 15957 0\n-508519 15973 0\n-508527 15889 0\n508531 -15889 -15985 0\n-508535 15989 0\n-508655 15893 0\n-508671 15893 0\n-509559 15989 0\n512099 -16001 -16097 0\n-512111 16109 0\n512115 -16001 -16113 0\n512363 -16009 -16105 0\n-512367 16109 0\n512379 -16009 -16121 0\n-512383 16009 0\n-512467 16081 0\n-512483 16013 0\n-512483 16097 0\n-512491 16105 0\n512495 -16013 -16109 0\n-512499 16013 0\n-512499 16113 0\n512511 -16013 -16125 0\n512595 -16017 -16081 0\n-512619 16105 0\n512627 -16017 -16113 0\n-512635 16017 0\n-513523 16045 0\n-516331 16133 0\n-516347 16133 0\n-516431 16137 0\n-516431 16205 0\n-516447 16221 0\n-516455 16229 0\n516459 -16137 -16233 0\n-516463 16137 0\n-516463 16237 0\n516475 -16137 -16249 0\n-516583 16229 0\n-516599 16245 0\n516607 -16141 -16253 0\n-516863 16149 0\n517119 -16157 -16253 0\n-517487 16169 0\n-517503 16169 0\n520291 -16257 -16353 0\n-520295 16357 0\n520307 -16257 -16369 0\n-520311 16373 0\n-520395 16329 0\n-520411 16345 0\n-520419 16353 0\n520423 -16261 -16357 0\n-520427 16361 0\n520439 -16261 -16373 0\n520447 -16261 -16381 0\n520523 -16265 -16329 0\n-520547 16353 0\n520555 -16265 -16361 0\n-520563 16369 0\n520571 -16265 -16377 0\n-520827 16273 0\n521083 -16281 -16377 0\n-521451 16293 0\n-521467 16293 0\n-521471 16293 0\n-524359 16453 0\n-524375 16469 0\n-524383 16477 0\n524387 -16385 -16481 0\n-524391 16485 0\n524411 -16385 -16505 0\n-524511 16389 0\n-524527 16389 0\n-524791 16501 0\n-525055 16405 0\n525311 -16413 -16509 0\n525411 -16417 -16481 0\n-525415 16485 0\n-525431 16501 0\n-525435 16505 0\n-525439 16417 0\n-525567 16421 0\n-526079 16437 0\n-526207 16441 0\n-528475 16601 0\n528483 -16513 -16609 0\n-528491 16617 0\n528499 -16513 -16625 0\n-528755 16521 0\n-528755 16625 0\n528763 -16521 -16633 0\n529011 -16529 -16625 0\n-529019 16529 0\n529275 -16537 -16633 0\n-529279 16537 0\n-529379 16541 0\n-529395 16541 0\n-529399 16541 0\n-529403 16541 0\n529407 -16541 -16637 0\n529507 -16545 -16609 0\n-529531 16545 0\n-530043 16561 0\n530167 -16565 -16629 0\n-530171 16565 0\n-532719 16645 0\n532975 -16653 -16749 0\n-532983 16757 0\n532991 -16653 -16765 0\n-533243 16661 0\n-533247 16661 0\n-533343 16665 0\n-533359 16749 0\n-533363 16665 0\n-533367 16757 0\n533371 -16665 -16761 0\n-533495 16757 0\n-534007 16757 0\n-534135 16757 0\n-536683 16873 0\n536691 -16769 -16881 0\n536939 -16777 -16873 0\n-536947 16777 0\n-536947 16881 0\n536955 -16777 -16889 0\n537203 -16785 -16881 0\n-537207 16785 0\n-537211 16785 0\n-537215 16785 0\n-537307 16789 0\n-537323 16789 0\n-537323 16873 0\n-537327 16789 0\n-537331 16789 0\n537335 -16789 -16885 0\n-537459 16793 0\n-537459 16881 0\n537467 -16793 -16889 0\n-537971 16809 0\n538095 -16813 -16877 0\n-538099 16813 0\n-540911 16901 0\n-541171 16909 0\n-541175 17013 0\n-541179 16909 0\n541183 -16909 -17021 0\n-541271 16981 0\n-541287 16997 0\n-541291 16913 0\n-541295 17005 0\n541299 -16913 -17009 0\n-541311 16913 0\n-541423 16917 0\n-541439 16917 0\n-541935 16933 0\n-542063 17005 0\n544867 -17025 -17121 0\n-544875 17129 0\n544883 -17025 -17137 0\n545131 -17033 -17129 0\n-545135 17033 0\n-545135 17133 0\n-545139 17033 0\n-545139 17137 0\n-545143 17033 0\n545147 -17033 -17145 0\n-545151 17033 0\n-545235 17105 0\n-545251 17121 0\n-545255 17037 0\n-545259 17129 0\n545263 -17037 -17133 0\n-545275 17037 0\n545279 -17037 -17149 0\n545363 -17041 -17105 0\n-545387 17041 0\n-545387 17129 0\n545395 -17041 -17137 0\n-545403 17041 0\n-545899 17129 0\n-546027 17129 0\n-549099 17157 0\n-549103 17157 0\n-549107 17157 0\n-549115 17157 0\n-549199 17161 0\n-549199 17229 0\n-549215 17245 0\n-549219 17161 0\n-549223 17253 0\n-549239 17269 0\n549243 -17161 -17273 0\n-549351 17253 0\n-549367 17269 0\n549375 -17165 -17277 0\n-549631 17173 0\n-549863 17253 0\n549887 -17181 -17277 0\n-549991 17253 0\n553059 -17281 -17377 0\n-553063 17381 0\n-553067 17385 0\n-553071 17389 0\n553075 -17281 -17393 0\n-553079 17397 0\n-553163 17353 0\n-553179 17369 0\n-553183 17373 0\n-553187 17377 0\n553191 -17285 -17381 0\n-553203 17393 0\n553207 -17285 -17397 0\n553215 -17285 -17405 0\n553291 -17289 -17353 0\n-553315 17377 0\n553323 -17289 -17385 0\n-553331 17393 0\n553339 -17289 -17401 0\n553471 -17293 -17405 0\n-553595 17297 0\n-553827 17377 0\n553851 -17305 -17401 0\n553951 -17309 -17373 0\n-553955 17377 0\n-557127 17477 0\n-557143 17493 0\n-557147 17497 0\n-557151 17501 0\n-557167 17517 0\n557179 -17409 -17529 0\n-557279 17413 0\n-557295 17413 0\n-557559 17525 0\n557567 -17421 -17533 0\n-557791 17429 0\n-557823 17429 0\n-557919 17433 0\n558047 -17437 -17501 0\n558079 -17437 -17533 0\n-561243 17625 0\n-561259 17641 0\n561267 -17537 -17649 0\n561399 -17541 -17653 0\n-561523 17545 0\n-561523 17649 0\n561531 -17545 -17657 0\n-561755 17553 0\n561779 -17553 -17649 0\n-561787 17553 0\n-561883 17557 0\n562011 -17561 -17625 0\n562043 -17561 -17657 0\n565363 -17665 -17777 0\n-565487 17773 0\n565495 -17669 -17781 0\n-565719 17749 0\n565743 -17677 -17773 0\n-565751 17781 0\n-565847 17681 0\n566007 -17685 -17781 0\n-569451 17897 0\n569459 -17793 -17905 0\n-569683 17873 0\n569707 -17801 -17897 0\n-569715 17905 0\n-569811 17873 0\n569971 -17809 -17905 0\n-573647 17997 0\n-573679 18029 0\n-573775 17997 0\n573903 -17933 -17997 0\n573935 -17933 -18029 0\n-577611 18121 0\n-577643 18153 0\n-577739 18121 0\n577867 -18057 -18121 0\n577899 -18057 -18153 0\n-581703 18245 0\n581831 -18181 -18245 0\n-14649 14713 0\n-14773 14837 0\n-14897 14961 0\n-15021 15085 0\n-15145 15209 0\n-15269 15333 0\n-15477 15365 0\n-15461 15365 0\n-15393 15457 0\n-15397 15461 0\n15613 0\n-15505 15601 0\n-15513 15609 0\n-15521 15585 0\n15741 0\n-15733 15621 0\n-15637 15733 0\n-15641 15737 0\n-15673 15737 0\n-15753 15865 0\n-15761 15857 0\n-15765 15861 0\n-15769 15865 0\n-15797 15861 0\n15997 0\n-15989 15877 0\n-15973 15877 0\n-15889 15985 0\n-15893 15989 0\n-15957 15893 0\n16001 0\n16125 0\n-16009 16121 0\n-16105 16009 0\n-16109 16013 0\n-16017 16113 0\n-16081 16017 0\n-16045 16109 0\n16253 0\n-16245 16133 0\n-16137 16249 0\n-16229 16133 0\n-16233 16137 0\n-16237 16141 0\n-16149 16245 0\n-16205 16141 0\n-16221 16157 0\n-16169 16233 0\n16257 0\n16381 0\n-16265 16377 0\n-16361 16265 0\n-16273 16369 0\n-16281 16377 0\n-16329 16265 0\n-16345 16281 0\n-16293 16357 0\n16385 0\n16509 0\n-16501 16389 0\n-16485 16389 0\n-16405 16501 0\n-16453 16389 0\n-16469 16405 0\n-16477 16413 0\n-16421 16485 0\n-16437 16501 0\n-16441 16505 0\n16513 0\n16637 0\n-16521 16633 0\n-16617 16521 0\n-16529 16625 0\n-16537 16633 0\n-16601 16537 0\n-16545 16609 0\n-16561 16625 0\n-16565 16629 0\n16765 0\n-16757 16645 0\n-16749 16653 0\n-16661 16757 0\n-16665 16761 0\n16769 0\n-16777 16889 0\n-16873 16777 0\n-16785 16881 0\n-16789 16885 0\n-16809 16873 0\n-16813 16877 0\n17021 0\n-17013 16901 0\n-16997 16901 0\n-17005 16909 0\n-16913 17009 0\n-16917 17013 0\n-16981 16917 0\n-16933 16997 0\n17025 0\n17149 0\n-17033 17145 0\n-17129 17033 0\n-17133 17037 0\n-17041 17137 0\n-17105 17041 0\n17277 0\n-17269 17157 0\n-17161 17273 0\n-17253 17157 0\n-17173 17269 0\n-17229 17165 0\n-17245 17181 0\n17281 0\n17405 0\n-17289 17401 0\n-17385 17289 0\n-17389 17293 0\n-17297 17393 0\n-17305 17401 0\n-17353 17289 0\n-17369 17305 0\n-17373 17309 0\n17409 0\n17533 0\n-17525 17413 0\n-17517 17421 0\n-17429 17525 0\n-17433 17529 0\n-17477 17413 0\n-17493 17429 0\n-17497 17433 0\n-17501 17437 0\n17537 0\n-17653 17541 0\n-17545 17657 0\n-17641 17545 0\n-17553 17649 0\n-17557 17653 0\n-17561 17657 0\n-17625 17561 0\n17665 0\n-17781 17669 0\n-17773 17677 0\n-17681 17777 0\n-17685 17781 0\n-17749 17685 0\n17793 0\n-17897 17801 0\n-17809 17905 0\n-17873 17809 0\n-18029 17933 0\n-17997 17933 0\n-18153 18057 0\n-18121 18057 0\n-18245 18181 0\n-16389 0\n16481 0\n" "636 d 376 0\n780 -16665 533371 0 316 562 0\n780 d 316 562 0\n781 -16537 529275 0 294 553 0\n781 d 294 553 0\n782 -16233 0 537 636 269 75 234 522 0\n782 d 75 234 522 0\n786 -15641 0 537 636 269 79 179 497 0\n786 d 79 179 497 0\n790 -16109 0 537 636 269 76 219 514 0\n790 d 76 219 514 0\n795 -18153 577899 0 477 632 0\n795 d 477 632 0\n796 -15753 504187 0 185 499 0\n796 d 185 499 0\n797 496255 -512115 0 494 635 1 2 3 4 197 790 209 48 49 796 174 184 173 38 0\n797 d 197 209 48 49 796 174 184 173 38 0\n798 -15765 0 537 636 269 78 191 501 0\n798 d 78 191 501 0\n803 -17553 561779 0 448 616 0\n803 d 448 0\n804 -16785 537203 0 326 566 0\n804 d 326 0\n805 -18029 573935 0 472 630 0\n805 d 472 630 0\n806 -17781 565495 0 455 621 0\n806 d 455 621 0\n807 -17897 569707 0 464 627 0\n807 d 464 627 0\n808 -17773 565743 0 457 622 0\n808 d 457 622 0\n809 -17385 553323 0 595 416 0\n809 d 416 0\n810 537211 -16777 -16793 0 578 635 9 10 11 559 12 561 13 571 311 14 344 383 564 325 338 60 123 359 809 364 402 36 0\n810 d 338 123 0\n811 -17129 545131 0 360 581 0\n811 d 360 0\n812 -17685 566007 0 460 624 0\n812 d 460 624 0\n813 -17033 545147 0 580 366 0\n813 d 580 366 0\n814 -17653 561399 0 443 613 0\n814 d 443 613 0\n815 -16789 537335 0 335 567 0\n815 d 335 567 0\n816 -18121 577867 0 476 633 0\n816 d 476 633 0\n817 -17997 573903 0 471 631 0\n817 d 471 631 0\n818 -16565 530167 0 304 557 0\n818 d 304 557 0\n819 -16813 538095 0 340 569 0\n819 d 340 569 0\n820 -18245 581831 0 479 634 0\n820 d 479 634 0\n821 -16913 541299 0 351 574 0\n821 d 351 574 0\n822 -17373 553951 0 423 601 0\n822 d 423 601 0\n823 -17161 549243 0 392 587 0\n823 d 392 587 0\n824 -553075 529279 530171 537207 553955 561883 565847 569811 573775 577739 581703 0 529 537 549 570 579 593 602 635 636 1 9 269 255 10 74 43 11 559 252 271 12 319 561 536 280 547 13 310 265 284 14 15 382 385 588 413 399 44 430 607 437 610 427 62 63 813 346 361 367 581 343 573 30 42 381 356 401 405 18 410 412 341 114 115 116 117 65 66 819 821 815 780 300 823 374 132 349 333 314 298 389 370 822 24 408 0\n825 -561531 561787 573679 577643 0 626 635 9 10 11 12 13 14 15 16 604 606 436 56 57 462 806 465 458 33 0\n826 -17809 569971 0 467 628 0\n826 d 467 628 0\n827 -525311 529019 529531 0 529 537 549 570 578 579 592 593 602 612 620 635 636 1 9 539 540 269 255 10 541 545 74 43 11 559 275 282 252 271 12 308 317 561 536 280 13 342 571 310 311 265 14 344 575 15 382 383 384 385 586 588 353 354 16 413 394 393 431 432 44 430 607 610 427 108 110 112 113 400 811 804 781 415 424 358 377 327 328 329 295 35 323 564 810 325 336 60 25 359 440 364 583 619 451 36 379 618 134 136 138 402 452 820 816 817 595 92 94 96 478 475 470 594 795 805 826 418 474 469 629 67 466 442 616 449 825 446 615 441 37 417 404 62 63 813 346 361 365 367 343 345 30 39 42 401 403 405 410 596 412 114 115 116 117 419 65 66 821 815 780 300 54 55 823 374 349 333 314 298 453 814 389 370 623 617 24 459 450 408 824 822 305 133 818 0\n827 d 824 0\n828 -17561 562043 0 618 452 0\n828 d 618 452 0\n829 -15673 501627 0 182 498 0\n829 d 182 498 0\n830 -15797 505591 0 195 503 0\n830 d 195 503 0\n831 17377 -17289 529379 529403 533343 537307 537331 537459 541295 545235 545259 545387 549199 557151 561243 0 537 635 636 1 9 540 269 2 10 278 545 74 3 11 559 282 252 4 12 315 317 536 505 13 571 263 207 14 575 15 588 353 576 16 390 393 347 431 608 425 782 527 243 790 517 227 409 415 27 25 281 302 277 555 140 141 301 830 829 196 183 19 406 142 414 0\n831 d 142 414 0\n832 -525411 529379 533343 537307 545235 549199 553163 0 537 635 636 1 9 540 269 2 10 278 74 3 11 252 4 12 536 505 13 571 263 207 14 575 15 576 16 347 608 425 782 527 243 790 517 227 140 141 830 829 196 183 19 0\n832 d 278 263 207 576 347 608 425 243 517 227 140 141 830 829 196 183 19 0\n833 -16361 520555 0 258 531 0\n833 d 258 0\n834 -16521 528763 0 291 550 0\n834 d 291 550 0\n835 -16009 512379 0 512 213 0\n835 d 512 213 0\n837 -16137 516475 0 237 520 0\n837 d 237 520 0\n838 520427 -520439 0 511 635 1 540 2 270 3 4 505 204 786 180 798 192 50 51 837 222 235 220 29 0\n838 d 235 220 0\n840 -15393 492643 0 158 488 0\n840 d 158 488 0\n841 508527 -16009 492671 -504435 524383 0 490 528 537 635 636 1 269 2 80 3 521 170 4 233 169 5 6 495 178 798 190 69 71 245 211 251 218 26 0\n842 -15761 504435 0 186 500 0\n842 d 186 500 0\n843 508527 -16009 492671 524383 0 490 504 528 537 635 636 1 269 2 74 80 3 228 521 252 170 4 233 246 169 5 6 495 178 496 175 790 212 798 190 835 47 199 198 841 842 187 28 166 492 165 70 72 245 211 251 218 26 0\n843 d 841 0\n844 -15889 0 537 636 269 77 203 507 0\n844 d 77 203 507 0\n846 17033 529399 533363 537215 537327 541179 541291 542063 545255 553955 569811 573775 577739 581703 0 529 537 593 602 620 635 636 1 9 269 255 10 74 43 11 559 252 271 12 319 536 280 547 13 265 284 14 15 384 385 588 413 399 44 430 607 437 610 427 365 367 581 39 42 381 403 405 596 412 419 65 54 55 823 453 814 389 623 617 24 459 450 408 822 132 133 819 818 341 305 18 0\n846 d 255 43 271 319 280 547 265 284 384 413 399 44 430 607 437 610 427 365 39 381 403 596 419 54 55 453 814 389 623 617 24 459 450 408 822 132 133 819 818 341 305 18 0\n847 -17545 561531 0 446 614 0\n847 d 446 614 0\n848 -16749 532975 0 560 307 0\n848 d 307 0\n849 -569707 -17401 529395 533359 537323 545251 0 537 585 635 636 1 9 539 269 10 279 74 11 252 12 536 13 572 264 14 348 15 16 604 606 609 426 782 527 244 87 398 591 388 22 407 600 422 86 0\n849 d 86 0\n850 -17401 529395 533359 537323 545251 553595 561523 0 537 585 635 636 1 9 539 269 10 279 74 11 252 12 536 13 572 264 14 348 15 586 16 589 604 396 433 606 609 426 782 527 244 849 807 461 32 454 808 89 398 591 388 22 407 600 422 88 0\n850 d 849 88 0\n851 537323 529395 533359 545251 553595 561523 0 537 585 635 636 1 9 539 269 10 279 74 11 252 12 536 13 572 264 14 348 15 586 16 589 604 396 433 606 609 426 782 527 244 850 598 600 407 22 388 591 398 87 89 807 808 461 454 32 0\n851 d 589 396 433 850 87 89 807 808 461 454 32 0\n852 17037 529279 533359 537207 541171 545251 553203 553595 0 549 603 635 9 10 11 559 12 561 13 310 14 15 382 586 391 373 582 362 30 401 410 114 115 117 821 815 300 352 331 297 40 851 429 444 605 847 434 58 0\n852 d 582 0\n853 -561531 -558079 561787 0 93 95 795 805 474 469 825 0\n853 d 93 95 0\n854 -16545 529507 0 555 301 0\n854 d 301 0\n855 -525311 520827 529379 529403 533343 537307 537331 541295 549199 553163 557151 561243 0 563 592 635 636 1 9 539 540 2 10 274 545 519 11 306 559 282 524 12 315 317 241 13 571 14 575 15 588 353 16 390 393 431 108 110 112 400 811 804 409 415 371 377 328 27 281 277 832 368 584 375 143 854 302 25 336 337 810 321 565 59 320 834 34 289 0\n855 d 315 390 409 27 281 277 832 375 143 854 0\n856 -16777 536955 0 564 325 0\n856 d 564 325 0\n857 -15269 488679 0 155 485 0\n857 d 155 485 0\n858 -16281 521083 0 262 533 0\n858 d 262 533 0\n859 -15145 484715 0 152 484 0\n859 d 152 484 0\n860 -15505 496243 0 163 491 0\n860 d 163 491 0\n861 -16265 520571 0 260 530 0\n861 d 260 530 0\n862 -529011 484735 488699 512483 0 490 518 537 635 636 1 539 269 2 541 80 3 543 170 4 267 168 5 506 6 201 7 8 486 160 786 177 798 189 105 858 535 250 21 232 526 242 106 0\n862 d 105 106 0\n863 512499 -528499 0 518 635 1 540 2 270 3 4 505 204 786 180 798 192 52 53 861 240 531 523 253 236 29 0\n863 d 270 204 180 192 523 236 29 0\n865 -17289 553339 0 418 594 0\n865 d 418 594 0\n866 -492643 512483 516447 520411 0 490 537 635 636 1 539 269 2 541 80 3 543 170 4 267 168 5 506 6 201 7 8 486 160 786 177 798 189 124 125 857 859 157 154 21 0\n866 d 543 267 168 506 201 486 160 177 189 21 0\n867 -15513 496507 0 165 492 0\n867 d 165 492 0\n868 -16017 512627 0 515 225 0\n868 d 225 0\n869 492671 524383 528491 0 490 504 528 537 635 636 1 273 269 2 74 80 3 228 229 519 521 252 170 4 239 233 246 169 5 505 6 508 495 206 178 496 175 790 212 798 190 844 202 843 214 513 41 218 248 26 254 251 838 245 253 69 70 833 842 867 83 187 166 868 28 226 198 31 199 259 46 247 0\n870 508403 -520291 0 537 635 636 1 269 2 74 3 228 252 4 246 5 6 495 496 175 790 212 69 70 842 867 187 166 28 0\n870 d 69 70 0\n871 -15021 480751 0 150 483 0\n871 d 150 483 0\n872 -14649 468859 0 144 480 0\n872 d 144 480 0\n873 -14897 476787 0 148 482 0\n873 d 148 482 0\n874 -14773 472823 0 146 481 0\n874 d 146 481 0\n875 -15521 496739 0 171 493 0\n875 d 171 493 0\n876 -15769 504699 0 194 502 0\n876 d 194 502 0\n877 16009 520419 520547 0 490 511 518 537 538 548 578 592 612 635 636 1 9 272 539 540 542 269 2 10 541 546 545 266 80 3 229 521 11 559 275 283 282 170 4 233 238 12 308 317 318 561 167 169 5 505 13 342 571 572 311 6 508 14 344 575 577 7 495 205 509 15 383 588 353 355 8 178 181 200 16 393 397 487 431 604 159 489 606 162 435 786 176 798 188 190 844 202 214 41 248 254 838 253 833 531 83 861 868 52 516 288 215 552 293 513 224 50 51 81 286 555 302 827 276 544 268 84 876 193 556 218 837 222 303 26 161 840 124 125 126 127 128 129 857 859 871 873 874 872 156 153 151 149 147 145 230 17 249 216 256 130 875 172 23 285 554 781 109 811 358 377 35 323 856 60 359 364 107 400 111 804 328 810 36 336 402 595 865 67 442 616 380 415 421 447 25 440 619 451 828 136 138 96 816 817 826 629 98 473 468 463 812 625 456 20 339 568 322 102 103 858 242 535 526 250 232 866 0\n877 d 540 546 545 283 282 233 317 318 169 577 588 353 355 178 393 397 431 435 190 513 50 51 81 84 556 218 837 222 303 26 230 216 256 130 107 111 380 415 421 447 25 98 473 468 463 812 625 456 20 339 568 0\n880 529019 520427 -525311 0 528 548 563 635 1 9 273 539 2 10 541 3 229 519 11 559 275 4 239 12 308 505 342 508 206 838 110 254 811 248 358 41 35 214 324 835 321 45 59 247 834 259 551 287 31 226 868 827 82 302 286 555 0\n880 d 827 82 302 286 555 0\n881 -17625 529279 537207 537215 545403 553955 561787 0 549 570 579 592 635 9 10 11 559 12 561 13 571 310 14 575 15 382 385 586 354 16 394 432 619 828 92 94 795 805 474 469 451 96 826 629 466 825 847 615 441 37 417 404 62 63 813 346 361 367 343 345 573 42 30 356 405 401 412 410 66 114 115 116 117 374 821 815 780 300 370 349 333 314 298 134 820 478 136 816 475 846 470 817 138 0\n881 d 451 96 825 134 136 138 0\n882 -553075 529279 537207 537215 553955 569811 573775 577739 581703 0 549 570 579 635 9 10 11 559 12 561 13 310 14 15 382 385 62 63 813 346 361 367 343 573 42 30 405 401 412 410 66 115 116 117 374 815 780 300 345 356 114 821 370 333 314 298 349 846 0\n882 d 345 356 114 370 333 314 298 349 846 0\n883 17393 529279 533359 537207 537323 545251 545403 561523 0 549 570 579 603 635 9 10 11 559 12 561 13 571 310 14 575 15 382 385 586 354 16 391 394 432 411 597 420 851 297 300 117 120 410 401 417 121 37 821 441 352 615 847 58 434 605 429 40 373 372 362 30 343 346 64 813 367 42 405 412 374 66 0\n883 d 575 586 354 391 394 432 417 121 37 821 441 352 615 58 434 605 429 40 373 374 66 0\n885 16777 -17289 -525311 529379 529403 533343 537307 537331 541295 544875 545387 549199 557151 561243 0 528 548 549 563 570 578 592 612 635 1 9 539 2 10 274 541 229 519 11 306 559 275 524 12 308 561 241 13 342 571 310 311 14 344 15 382 383 323 565 108 110 112 113 865 35 320 332 400 811 804 781 67 293 371 327 328 295 442 552 445 288 292 52 100 104 861 357 848 531 369 313 253 838 254 248 41 214 835 45 247 532 261 34 289 834 59 321 337 831 368 584 583 378 122 809 402 36 363 813 62 64 404 346 411 597 343 420 851 852 297 300 117 120 410 372 401 362 30 0\n885 d 337 0\n886 557151 -17289 -525311 529379 529403 533343 537307 537331 541295 544875 545259 545387 549199 561243 0 578 592 108 112 400 804 328 885 856 60 359 583 810 584 336 368 831 0\n886 d 885 810 584 336 368 831 0\n887 -553075 -525311 529279 529379 529403 533343 537207 537307 537331 541295 544875 545139 545259 545387 545403 549199 0 592 603 612 635 9 10 11 559 12 561 13 571 311 14 344 383 112 804 328 36 402 595 865 67 442 108 329 616 449 400 424 881 440 886 428 611 439 438 97 135 137 139 826 820 816 817 629 478 475 470 466 882 0\n887 d 108 329 616 400 424 881 886 438 97 135 137 139 826 820 816 817 629 478 475 470 466 882 0\n889 -520307 0 504 528 45 835 46 199 198 870 245 257 877 251 0\n889 d 45 46 877 251 0\n895 544875 -16361 0 528 548 563 635 1 9 273 539 2 10 541 3 519 11 559 275 4 239 12 308 505 342 508 206 889 247 259 531 861 52 288 552 293 35 324 321 59 834 551 287 31 226 868 833 83 0\n895 d 833 83 0\n897 -16529 484735 488699 0 510 548 552 288 292 863 862 217 208 73 860 164 797 210 221 0\n897 d 863 862 221 0\n898 524383 544875 0 510 518 528 563 635 1 9 273 539 2 10 274 541 3 229 519 11 306 559 275 4 239 524 12 308 505 241 342 508 206 844 202 889 247 259 532 261 895 253 838 254 248 41 214 843 161 840 124 125 857 859 157 154 897 293 35 323 324 321 59 834 551 287 31 226 515 210 797 164 860 73 208 217 289 34 320 322 102 103 858 242 535 526 250 232 866 0\n898 d 541 275 308 342 157 154 897 35 323 324 289 0\n899 -536939 -492643 512483 0 518 102 103 858 242 535 526 250 232 866 0\n899 d 102 103 858 242 535 526 250 232 866 0\n901 -16873 536939 0 565 322 0\n901 d 322 0\n902 528491 512483 524383 528475 0 490 504 518 528 537 548 635 636 1 9 272 273 539 542 269 2 10 274 266 74 80 3 228 229 519 521 306 252 170 4 239 524 238 246 167 5 505 241 6 508 7 495 205 206 509 8 181 496 200 487 175 159 489 162 786 176 790 212 798 188 889 247 259 532 261 31 226 868 85 876 193 869 161 840 124 125 126 127 128 129 857 859 871 873 874 872 156 153 151 149 147 145 899 901 320 34 290 288 52 53 861 240 531 534 525 253 249 231 838 17 254 215 248 223 41 131 214 875 835 172 47 199 198 870 245 257 23 224 211 71 72 842 867 187 166 28 0\n902 d 869 899 0\n903 -528499 524383 528475 0 490 504 518 528 537 635 636 1 272 542 269 2 266 74 80 3 228 229 521 252 170 4 238 246 167 5 505 6 508 7 495 205 509 8 181 496 200 487 175 159 489 162 786 176 790 212 798 188 844 202 52 53 861 240 531 253 534 525 838 249 231 254 248 41 214 835 843 47 161 199 840 198 124 125 126 127 128 129 870 857 859 871 873 874 872 245 156 153 151 149 147 145 257 17 215 516 223 868 131 85 875 876 172 193 23 224 211 71 72 842 867 187 166 28 0\n903 d 272 542 266 80 228 229 521 170 238 246 167 5 6 7 495 205 509 8 181 496 200 487 175 159 489 162 176 212 188 202 52 53 861 240 531 534 525 838 249 231 254 248 41 214 835 843 47 161 199 840 198 124 125 126 127 128 129 870 857 859 871 873 874 872 245 156 153 151 149 147 145 257 17 215 516 223 868 131 85 875 876 172 193 23 224 211 71 72 842 867 187 166 28 0\n904 512483 -17129 0 528 538 548 558 563 570 578 592 612 635 1 9 539 2 10 274 519 11 306 559 524 12 561 241 13 571 310 311 14 344 15 382 383 889 247 532 261 811 581 109 110 813 781 276 62 64 295 554 544 404 346 285 268 411 597 343 903 420 288 290 34 320 901 565 99 856 357 60 61 369 359 309 364 583 560 379 313 902 287 551 834 59 321 566 327 328 852 36 402 595 865 67 442 445 883 331 815 115 118 410 372 401 362 30 0\n904 d 902 0\n905 529019 544875 0 538 898 268 544 276 895 880 253 0\n905 d 895 880 253 0\n906 -17129 0 510 528 538 548 558 563 570 578 592 612 635 1 9 273 539 2 10 274 3 519 11 306 559 4 239 524 12 561 505 241 13 571 310 311 508 14 344 206 15 382 383 889 247 259 532 261 811 581 813 62 64 404 346 411 597 343 420 904 109 781 295 110 276 544 268 217 554 208 285 73 903 860 288 164 290 797 34 210 320 901 515 565 99 357 369 226 856 31 60 61 287 359 583 379 309 551 364 560 313 834 59 321 566 327 328 852 36 402 595 865 67 442 445 883 331 815 115 118 410 372 401 362 30 0\n906 d 273 2 274 3 519 306 4 239 524 505 241 508 206 259 811 581 904 109 110 217 554 208 285 73 903 860 288 164 290 797 34 210 320 515 565 99 226 856 31 60 61 287 359 309 551 364 560 834 59 321 566 331 0\n1014 545403 561523 0 538 549 570 578 592 635 9 10 11 559 12 561 13 310 14 15 382 385 906 358 371 377 898 905 268 293 544 552 276 292 112 113 100 101 104 804 781 357 901 848 327 295 369 332 313 883 404 62 813 363 63 346 343 573 350 361 30 401 410 115 116 117 815 780 300 330 334 312 296 299 367 887 42 386 405 823 412 65 0\n1014 d 385 371 377 883 63 361 367 887 42 386 405 823 412 65 0\n1015 561523 0 538 549 570 578 592 635 9 10 11 559 12 561 13 571 310 311 14 344 15 382 383 906 358 898 905 268 293 544 552 276 292 112 113 100 101 104 804 781 357 901 848 327 328 295 369 332 313 1014 379 583 378 122 809 402 36 363 813 62 64 404 346 411 597 343 420 852 851 297 300 117 120 410 372 401 362 30 0\n1015 d 1014 379 583 378 122 809 851 0\n1074 -17305 553851 0 422 598 0\n1074 d 422 598 0\n1075 529395 -561779 0 537 578 585 635 636 1 9 539 269 10 279 74 11 252 12 536 13 572 264 14 348 15 16 604 606 609 426 782 527 244 906 358 905 293 552 292 100 101 104 357 901 848 369 332 313 90 91 1074 398 600 591 407 388 22 0\n1075 d 1 539 269 279 74 252 536 572 264 348 609 426 527 244 101 901 332 90 91 1074 398 600 591 407 388 22 0\n1076 -545263 0 528 538 549 570 585 603 612 626 635 9 10 11 559 12 561 13 571 311 14 344 15 383 16 604 606 436 889 247 532 261 906 358 898 268 544 276 112 804 328 1015 444 445 847 442 56 57 67 68 462 806 865 395 465 458 595 599 590 402 406 387 36 363 813 64 346 573 350 118 815 330 334 119 780 312 120 300 296 297 299 1075 803 449 853 439 611 428 855 440 619 828 92 94 795 805 474 469 33 0\n1076 d 118 119 120 0\n1153 0 528 538 549 570 578 585 592 603 612 626 635 9 10 11 559 12 561 13 571 310 311 14 344 15 382 383 16 604 606 436 889 247 532 261 906 358 898 905 268 293 544 552 276 292 112 113 100 104 804 781 357 848 327 328 295 369 313 1015 444 445 847 442 56 57 67 68 462 806 865 395 465 458 595 599 590 402 406 387 36 363 813 62 64 404 346 411 597 343 573 420 852 350 1076 372 362 30 401 410 115 116 117 815 780 300 330 334 312 296 297 299 1075 803 449 853 439 611 428 855 440 619 828 92 94 795 805 474 469 33 0\n"


theorem rt1t32_refute_24 (x : ℤ → ℕ → Bool) (hm : RT1T32.Model x) (h1 : x 0 1 = false)
    (hJ : x 0 24 = true) : False := by
  have hF : (RT1T32.rval x).satisfies_fmla RT1T32.c24.formula :=
    RT1T32.s_fmla x hm 24 (by norm_num) h1 hJ _ (by decide +kernel)
  exact RT1T32.c24.sat_proof _ hF

rt1t32_lrat_core RT1T32.c28 "p cnf 536939 185\n16261 16389 0\n-16133 -16261 0\n15749 15877 0\n-15621 -15749 0\n15493 15621 0\n-15365 -15493 0\n528467 488827 492791 516575 484863 500719 508647 512611 504683 520539 524503 496755 0\n520427 504571 508535 512499 500607 516463 524391 0\n528491 512635 516599 520563 524527 508671 0\n536683 532719 524791 516863 520827 528755 0\n496255 504183 500219 508147 512111 0\n479871 487799 495727 491763 483835 0\n508543 524399 516471 512507 520435 0\n512383 520311 516347 0\n-508159 -512123 0\n-499835 -495871 0\n-520307 -512379 0\n-504187 -512115 0\n-504055 -508019 0\n-496127 -508019 0\n-496127 -504055 0\n-487803 -495731 0\n-483839 -495731 0\n-520439 -524403 0\n-516475 -524403 0\n-512511 -524403 0\n-520571 -528499 0\n-516607 -528499 0\n-524799 -528763 0\n-512099 -496243 0\n-504171 -496243 0\n-500207 -496243 0\n-479859 -495715 0\n-520555 -512627 0\n-529011 -536939 0\n-536939 -521083 0\n-517119 -536939 0\n-529011 -532975 0\n-532975 -521083 0\n-517119 -532975 0\n479859 -14993 -15089 0\n-479871 14993 0\n-483835 15117 0\n483839 -15117 -15229 0\n-484863 15149 0\n-487799 15241 0\n487803 -15241 -15353 0\n-488827 15273 0\n-488827 15353 0\n-491763 15365 0\n-492791 15477 0\n495715 -15489 -15585 0\n-495727 15597 0\n495731 -15489 -15601 0\n495871 -15493 -15613 0\n496127 -15501 -15613 0\n496243 -15505 -15601 0\n-496255 15505 0\n-496755 15521 0\n499835 -15617 -15737 0\n500207 -15629 -15725 0\n-500219 15737 0\n-500607 15641 0\n-500719 15725 0\n504055 -15749 -15861 0\n504171 -15753 -15849 0\n-504183 15753 0\n-504183 15861 0\n504187 -15753 -15865 0\n-504571 15765 0\n-504683 15849 0\n508019 -15873 -15985 0\n-508147 15877 0\n508159 -15877 -15997 0\n-508535 15989 0\n-508543 15889 0\n-508647 15973 0\n-508671 15893 0\n512099 -16001 -16097 0\n-512111 16109 0\n512115 -16001 -16113 0\n512123 -16001 -16121 0\n512379 -16009 -16121 0\n-512383 16009 0\n-512499 16013 0\n-512507 16013 0\n512511 -16013 -16125 0\n-512611 16097 0\n512627 -16017 -16113 0\n-512635 16017 0\n-516347 16133 0\n-516463 16137 0\n-516463 16237 0\n-516471 16245 0\n516475 -16137 -16249 0\n-516575 16221 0\n-516599 16245 0\n516607 -16141 -16253 0\n-516863 16149 0\n517119 -16157 -16253 0\n520307 -16257 -16369 0\n-520311 16373 0\n-520427 16361 0\n-520435 16369 0\n520439 -16261 -16373 0\n-520539 16265 0\n-520539 16345 0\n520555 -16265 -16361 0\n-520563 16369 0\n520571 -16265 -16377 0\n-520827 16273 0\n521083 -16281 -16377 0\n-524391 16485 0\n-524399 16493 0\n524403 -16385 -16497 0\n-524503 16389 0\n-524527 16389 0\n-524791 16501 0\n524799 -16397 -16509 0\n-528467 16593 0\n-528491 16617 0\n528499 -16513 -16625 0\n-528755 16521 0\n-528755 16625 0\n528763 -16521 -16633 0\n529011 -16529 -16625 0\n-532719 16749 0\n532975 -16653 -16749 0\n-536683 16873 0\n536939 -16777 -16873 0\n-14993 15089 0\n15229 0\n-15213 15117 0\n-15149 15213 0\n-15241 15353 0\n-15337 15241 0\n-15273 15337 0\n-15477 15365 0\n15489 0\n15613 0\n-15597 15501 0\n-15505 15601 0\n-15521 15585 0\n15617 0\n-15725 15629 0\n-15641 15737 0\n-15753 15865 0\n-15849 15753 0\n-15765 15861 0\n15873 0\n15997 0\n-15989 15877 0\n-15973 15877 0\n-15889 15985 0\n-15893 15989 0\n16001 0\n16125 0\n-16009 16121 0\n-16109 16013 0\n-16017 16113 0\n16253 0\n-16245 16133 0\n-16137 16249 0\n-16237 16141 0\n-16149 16245 0\n-16221 16157 0\n16257 0\n-16265 16377 0\n-16361 16265 0\n-16273 16369 0\n-16345 16281 0\n16385 0\n16509 0\n-16501 16389 0\n-16485 16389 0\n-16493 16397 0\n16513 0\n-16521 16633 0\n-16617 16521 0\n-16529 16625 0\n-16593 16529 0\n-16749 16653 0\n-16873 16777 0\n-16389 0\n16497 0\n" "185 d 0\n186 -528755 0 140 144 150 151 156 157 161 167 172 173 177 184 185 1 175 115 2 113 24 26 91 162 105 87 94 102 85 86 14 84 158 82 83 15 17 74 101 3 152 104 4 75 5 55 16 60 146 63 124 122 27 28 98 164 93 123 178 125 29 119 176 114 13 76 154 72 19 65 149 70 8 103 169 168 110 0\n186 d 124 123 0\n187 -528499 504571 0 140 144 151 156 157 161 172 184 185 1 175 115 2 113 24 26 91 105 87 102 85 14 84 158 82 15 74 3 152 4 75 5 55 16 60 146 63 27 28 98 164 93 8 103 169 168 110 0\n187 d 27 28 98 164 93 110 0\n188 -16017 512627 0 160 89 0\n188 d 89 0\n189 -488827 487803 0 48 49 137 47 136 0\n189 d 48 49 137 136 0\n190 -15725 500207 0 61 145 0\n190 d 61 145 0\n191 -15849 504171 0 148 66 0\n191 d 66 0\n192 -532975 -16377 484863 488827 496755 500719 504683 512611 528467 0 151 156 161 172 184 185 1 116 115 2 24 91 105 102 14 84 158 82 15 74 3 153 4 77 5 6 138 51 39 40 112 100 171 166 107 96 7 0\n192 d 39 0\n193 -16749 532975 0 128 182 0\n193 d 128 182 0\n194 -16377 484863 488827 496755 500719 504683 512611 528467 0 151 156 161 167 172 184 185 1 116 174 115 2 118 24 91 162 105 165 102 99 14 84 158 82 83 15 17 74 101 3 153 170 4 77 111 5 6 138 51 186 192 193 127 10 129 183 130 37 100 166 96 7 36 107 112 171 0\n194 d 192 36 107 112 171 0\n195 -16137 0 172 185 115 25 163 95 0\n195 d 25 163 95 0\n196 -14993 479859 0 131 41 0\n196 d 131 41 0\n197 -508019 0 132 139 140 144 151 156 157 172 177 184 185 1 175 115 2 113 24 26 91 105 87 102 85 159 14 80 84 158 82 15 74 3 73 152 4 75 5 6 55 50 16 60 62 146 63 195 92 20 56 141 53 19 65 149 70 8 103 169 168 68 11 58 142 54 57 22 23 30 32 189 44 79 190 43 133 88 64 134 45 187 31 122 180 181 120 191 71 194 59 143 52 33 196 42 12 46 135 47 0\n197 d 20 19 68 187 31 122 191 0\n198 -16521 0 150 157 167 172 173 184 185 1 115 2 24 26 91 162 105 87 94 102 86 14 84 158 83 17 101 104 197 72 154 76 13 114 176 119 29 178 125 0\n198 d 94 86 104 72 154 76 13 114 176 119 29 178 125 0\n199 -15753 0 151 156 167 172 184 185 1 117 115 2 24 91 162 105 97 102 14 84 158 82 83 15 17 74 101 152 109 155 78 198 179 121 9 90 160 81 18 147 69 0\n199 d 160 81 18 147 69 0\n200 -517119 0 167 172 184 185 1 174 115 2 118 24 91 162 105 165 102 99 14 84 158 83 17 101 170 111 186 40 193 127 10 129 183 130 37 0\n200 d 40 37 0\n201 -16361 0 151 156 167 172 184 185 1 117 115 2 24 91 162 105 97 102 14 84 158 82 83 15 17 74 101 152 109 155 78 198 179 121 9 90 188 34 169 108 0\n201 d 117 97 109 155 78 179 121 9 90 188 34 169 108 0\n202 -15241 0 139 140 144 151 156 157 172 184 185 1 115 2 24 26 91 105 87 102 159 14 80 84 158 82 15 74 3 73 4 5 55 16 60 62 199 67 11 58 142 54 22 135 47 0\n202 d 135 47 0\n203 528467 0 132 139 140 144 151 156 157 161 172 184 185 1 116 175 115 2 113 24 26 91 105 87 102 85 159 14 80 84 158 82 15 74 3 73 152 153 4 75 77 5 6 55 50 138 16 51 60 62 146 63 195 92 199 67 148 11 71 58 142 54 57 22 23 30 32 189 44 79 190 43 133 88 64 134 45 200 100 166 96 201 103 8 70 149 65 21 56 141 53 202 46 12 42 196 33 52 143 59 7 194 106 168 0\n203 d 116 175 113 26 87 85 159 80 82 15 74 3 73 152 153 4 75 77 5 6 55 50 138 16 51 60 62 146 63 92 67 148 11 71 58 142 54 57 22 23 30 32 189 44 79 190 43 133 88 64 134 45 100 166 96 103 8 70 149 65 21 56 141 53 46 12 42 196 33 52 143 59 7 194 106 168 0\n205 0 167 172 184 185 1 174 115 2 118 24 91 162 105 165 102 99 14 84 158 83 17 101 170 111 186 203 120 181 180 126 35 38 193 127 10 129 130 183 0\n"


theorem rt1t32_refute_28 (x : ℤ → ℕ → Bool) (hm : RT1T32.Model x) (h1 : x 0 1 = false)
    (hJ : x 0 28 = true) : False := by
  have hF : (RT1T32.rval x).satisfies_fmla RT1T32.c28.formula :=
    RT1T32.s_fmla x hm 28 (by norm_num) h1 hJ _ (by decide +kernel)
  exact RT1T32.c28.sat_proof _ hF


theorem rt1t32_endpoint_bits (x : ℤ → ℕ → Bool) (hm : RT1T32.Model x) :
    ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(4+1) - 1 → j ≠ 2^4 - 1 → j ≠ 2^4 →
      x p j = false := by
  intro p hp1 j hj0 hj31 hj15 hj16
  have hb : ∀ J, (∀ y : ℤ → ℕ → Bool, RT1T32.Model y → y 0 1 = false → y 0 J = true → False) →
      x p J = false := by
    intro J hr
    by_contra hc
    exact hr _ (RT1T32.model_shift x hm p) (by simpa using hp1) (by simpa using hc)
  have b3 := hb 3 (rt1t32_refute_3)
  have b7 := hb 7 (rt1t32_refute_7)
  have b24 := hb 24 (rt1t32_refute_24)
  have b28 := hb 28 (rt1t32_refute_28)
  have b30 : x p 30 = false := by
    have h := hm.2.1 1 (by norm_num) p
    rw [show (2:ℕ)^1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at h
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one] at h
    rw [show (0:ℕ) + 2^(4+1) - 2 = 30 from rfl, show (1:ℕ) + 2^(4+1) - 2 = 31 from rfl] at h
    have ha := hm.2.2.2 (p - 1)
    rw [sub_add_cancel, hp1] at ha
    have hx : x (p - 1) 1 = true := by
      revert ha; cases x (p - 1) 1 <;> simp
    have e0 := (RT1T32.end_ok x hm p).1
    have e31 := (RT1T32.end_ok x hm (p - 1)).2
    rw [e0, e31, hx] at h
    revert h; cases x p 30 <;> simp
  by_contra hc
  have hj : x p j = true := by simpa using hc
  simp only [show (2:ℕ)^(4+1) - 1 = 31 from rfl, show (2:ℕ)^4 = 16 from rfl] at hj31 hj15 hj16
  interval_cases j
  · have := hj; rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 2 30 (by decide) hj); rw [b30] at this; exact absurd this (by simp)
  · have := hj; rw [b3] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 4 28 (by decide) hj); rw [b28] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 29 1 (by decide) (RT1T32.par_ok x hm p 5 29 (by decide) hj)); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 6 30 (by decide) hj); rw [b30] at this; exact absurd this (by simp)
  · have := hj; rw [b7] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 8 24 (by decide) hj); rw [b24] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 25 1 (by decide) (RT1T32.par_ok x hm p 9 25 (by decide) hj)); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 2 30 (by decide) (RT1T32.par_ok x hm p 26 2 (by decide) (RT1T32.par_ok x hm p 10 26 (by decide) hj))); rw [b30] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 27 3 (by decide) (RT1T32.par_ok x hm p 11 27 (by decide) hj)); rw [b3] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 12 28 (by decide) hj); rw [b28] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 29 1 (by decide) (RT1T32.par_ok x hm p 13 29 (by decide) hj)); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 14 30 (by decide) hj); rw [b30] at this; exact absurd this (by simp)
  · exact absurd rfl hj15
  · exact absurd rfl hj16
  · have := (RT1T32.par_ok x hm p 17 1 (by decide) hj); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 2 30 (by decide) (RT1T32.par_ok x hm p 18 2 (by decide) hj)); rw [b30] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 19 3 (by decide) hj); rw [b3] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 4 28 (by decide) (RT1T32.par_ok x hm p 20 4 (by decide) hj)); rw [b28] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 29 1 (by decide) (RT1T32.par_ok x hm p 5 29 (by decide) (RT1T32.par_ok x hm p 21 5 (by decide) hj))); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 6 30 (by decide) (RT1T32.par_ok x hm p 22 6 (by decide) hj)); rw [b30] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 23 7 (by decide) hj); rw [b7] at this; exact absurd this (by simp)
  · have := hj; rw [b24] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 25 1 (by decide) hj); rw [hp1] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 2 30 (by decide) (RT1T32.par_ok x hm p 26 2 (by decide) hj)); rw [b30] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 27 3 (by decide) hj); rw [b3] at this; exact absurd this (by simp)
  · have := hj; rw [b28] at this; exact absurd this (by simp)
  · have := (RT1T32.par_ok x hm p 29 1 (by decide) hj); rw [hp1] at this; exact absurd this (by simp)
  · have := hj; rw [b30] at this; exact absurd this (by simp)

theorem cycle_power_thirty_one_endpoint_bits_of_alternating (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1) :
    ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(4+1) - 1 → j ≠ 2^4 - 1 → j ≠ 2^4 →
      x p j = false := by
  exact rt1t32_endpoint_bits x ⟨htight, hexact, hcover, halt⟩
