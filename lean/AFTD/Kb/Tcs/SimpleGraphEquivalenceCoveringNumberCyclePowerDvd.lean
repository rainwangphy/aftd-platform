import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerGe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.Bit

/-!
# simple_graph_equivalence_covering_number_cycle_power_dvd

Topic: combinatorics   Node: e5df1c48e542

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Theorem 2.6.

For k ≥ 1 and q ≥ 2, the k-th power of the cycle on q(k + 1) vertices has equivalence covering number exactly 1 + ⌈log₂(k + 1)⌉.
-/

/-- The label of vertex `i` in the `ℓ`-th binary-digit subgraph: blocks of `K` vertices,
`D = (i mod K) / 2^ℓ`; odd `D` joins its own block's class, even `D` the previous one. -/
def simple_graph_equivalence_covering_number_cycle_power_dvd_lab (q K ℓ i : ℕ) : ℕ :=
  ((i / K + q - 1 + (i % K / 2 ^ ℓ) % 2) % q) * K + (i % K / 2 ^ ℓ) / 2

/-- Two numbers `b < a < 2^L` agree above some bit `ℓ < L` where `a` has a one and `b` a zero. -/
theorem simple_graph_equivalence_covering_number_cycle_power_dvd_bits :
    ∀ (L a b : ℕ), b < a → a < 2 ^ L → ∃ ℓ, ℓ < L ∧ ∃ p, a / 2 ^ ℓ = 2 * p + 1 ∧ b / 2 ^ ℓ = 2 * p := by
  intro L
  induction L with
  | zero => intro a b hab ha; simp at ha; omega
  | succ L ih =>
    intro a b hab ha
    by_cases h2 : a / 2 = b / 2
    · exact ⟨0, by omega, a / 2, by simp; omega, by simp; omega⟩
    · have hle : b / 2 ≤ a / 2 := Nat.div_le_div_right hab.le
      have ha2 : a / 2 < 2 ^ L := by rw [pow_succ] at ha; omega
      obtain ⟨ℓ, hℓ, p, hp1, hp2⟩ := ih (a / 2) (b / 2) (by omega) ha2
      refine ⟨ℓ + 1, by omega, p, ?_, ?_⟩
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact hp1
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact hp2

theorem simple_graph_equivalence_covering_number_cycle_power_dvd_decode (K J r : ℕ) (hK : 0 < K)
    (hr : r < K) : (J * K + r) / K = J ∧ (J * K + r) % K = r := by
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hr, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- Labels that agree come from vertices at cyclic distance at most `k`. -/
theorem simple_graph_equivalence_covering_number_cycle_power_dvd_sound (k q : ℕ) (hq : 2 ≤ q)
    (i i' : ℕ) (hi : i < q * (k + 1)) (hi' : i' < q * (k + 1)) (hne : i ≠ i') (s : ℕ)
    (heq : (if s = 0 then i / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i) =
      (if s = 0 then i' / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i')) :
    ∃ d, 1 ≤ d ∧ d ≤ k ∧ ((i + d) % (q * (k + 1)) = i' ∨ (i' + d) % (q * (k + 1)) = i) := by
  have hK : 0 < k + 1 := by omega
  have hdi := Nat.div_add_mod' i (k + 1)
  have hdi' := Nat.div_add_mod' i' (k + 1)
  have hmi := Nat.mod_lt i hK
  have hmi' := Nat.mod_lt i' hK
  have hjq : ∀ m, m < q * (k + 1) → m / (k + 1) < q := fun m hm =>
    (Nat.div_lt_iff_lt_mul hK).mpr hm
  have hji := hjq i hi
  have hji' := hjq i' hi'
  have hz0 := Nat.zero_le (i / (k + 1))
  have hz0' := Nat.zero_le (i' / (k + 1))
  -- same block
  have hsame : i / (k + 1) = i' / (k + 1) →
      ∃ d, 1 ≤ d ∧ d ≤ k ∧ ((i + d) % (q * (k + 1)) = i' ∨ (i' + d) % (q * (k + 1)) = i) := by
    intro hj
    rw [hj] at hdi
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨i' - i, by omega, by omega, Or.inl (by rw [show i + (i' - i) = i' by omega,
        Nat.mod_eq_of_lt hi'])⟩
    · exact ⟨i - i', by omega, by omega, Or.inr (by rw [show i' + (i - i') = i by omega,
        Nat.mod_eq_of_lt hi])⟩
  -- the oriented cross-block case
  have hcross : ∀ m m' : ℕ, m < q * (k + 1) → m' < q * (k + 1) → ∀ ℓ,
      (m % (k + 1) / 2 ^ ℓ) % 2 = 1 → (m' % (k + 1) / 2 ^ ℓ) % 2 = 0 →
      simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) ℓ m =
        simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) ℓ m' →
      ∃ d, 1 ≤ d ∧ d ≤ k ∧ (m + d) % (q * (k + 1)) = m' := by
    intro m m' hm hm' ℓ h1 h0 hl
    unfold simple_graph_equivalence_covering_number_cycle_power_dvd_lab at hl
    rw [h1, h0] at hl
    have hdm := Nat.div_add_mod' m (k + 1)
    have hdm' := Nat.div_add_mod' m' (k + 1)
    have hmm := Nat.mod_lt m hK
    have hmm' := Nat.mod_lt m' hK
    have hjm := hjq m hm
    have hjm' := hjq m' hm'
    have hz := Nat.zero_le (m / (k + 1))
    have hz' := Nat.zero_le (m' / (k + 1))
    have hD : m % (k + 1) / 2 ^ ℓ ≤ m % (k + 1) := Nat.div_le_self _ _
    have hD' : m' % (k + 1) / 2 ^ ℓ ≤ m' % (k + 1) := Nat.div_le_self _ _
    have hq0 : 0 < q := by omega
    have hJ := Nat.mod_lt (m / (k + 1) + q - 1 + 1) hq0
    have hJ' := Nat.mod_lt (m' / (k + 1) + q - 1 + 0) hq0
    obtain ⟨hJJ, hpp⟩ := (by
      have e1 := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        ((m / (k + 1) + q - 1 + 1) % q) (m % (k + 1) / 2 ^ ℓ / 2) hK (by omega)
      have e2 := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        ((m' / (k + 1) + q - 1 + 0) % q) (m' % (k + 1) / 2 ^ ℓ / 2) hK (by omega)
      rw [hl] at e1
      exact ⟨e1.1.symm.trans e2.1, e1.2.symm.trans e2.2⟩ :
      (m / (k + 1) + q - 1 + 1) % q = (m' / (k + 1) + q - 1 + 0) % q ∧
        m % (k + 1) / 2 ^ ℓ / 2 = m' % (k + 1) / 2 ^ ℓ / 2)
    have hJm : (m / (k + 1) + q - 1 + 1) % q = m / (k + 1) := by
      rw [show m / (k + 1) + q - 1 + 1 = m / (k + 1) + q by have := Nat.zero_le (m / (k + 1)); omega,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt hjm]
    rw [hJm] at hJJ
    -- the digit of m is one more than that of m', so m % K > m' % K
    have hlt : m' % (k + 1) < m % (k + 1) := by
      by_contra hc
      push_neg at hc
      have := Nat.div_le_div_right (c := 2 ^ ℓ) hc
      omega
    have hmul : (m / (k + 1) + 1) * (k + 1) = m / (k + 1) * (k + 1) + (k + 1) := by ring
    refine ⟨k + 1 + m' % (k + 1) - m % (k + 1), by omega, by omega, ?_⟩
    by_cases hj0 : m' / (k + 1) = 0
    · -- wrap-around: m is in the last block
      rw [hj0] at hJJ
      have hlast : m / (k + 1) = q - 1 := by
        rw [show 0 + q - 1 + 0 = q - 1 by omega, Nat.mod_eq_of_lt (by omega)] at hJJ
        exact hJJ
      have hqK : (q - 1) * (k + 1) + (k + 1) = q * (k + 1) := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [hlast] at hdm
      rw [hj0] at hdm'
      rw [show m + (k + 1 + m' % (k + 1) - m % (k + 1)) = q * (k + 1) + m' by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hm']
    · have hprev : m / (k + 1) + 1 = m' / (k + 1) := by
        rw [show m' / (k + 1) + q - 1 + 0 = (m' / (k + 1) - 1) + q by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at hJJ
        omega
      rw [← hprev] at hdm'
      rw [show m + (k + 1 + m' % (k + 1) - m % (k + 1)) = m' by omega, Nat.mod_eq_of_lt hm']
  by_cases hs : s = 0
  · simp only [hs, if_true] at heq
    exact hsame (Nat.eq_of_mul_eq_mul_right hK heq)
  · simp only [hs, if_false] at heq
    by_cases hpar : (i % (k + 1) / 2 ^ (s - 1)) % 2 = (i' % (k + 1) / 2 ^ (s - 1)) % 2
    · apply hsame
      unfold simple_graph_equivalence_covering_number_cycle_power_dvd_lab at heq
      rw [hpar] at heq
      have hq0 : 0 < q := by omega
      have e1 := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        ((i / (k + 1) + q - 1 + i' % (k + 1) / 2 ^ (s - 1) % 2) % q)
        (i % (k + 1) / 2 ^ (s - 1) / 2) hK
        (by have := Nat.div_le_self (i % (k + 1)) (2 ^ (s - 1)); omega)
      have e2 := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        ((i' / (k + 1) + q - 1 + i' % (k + 1) / 2 ^ (s - 1) % 2) % q)
        (i' % (k + 1) / 2 ^ (s - 1) / 2) hK
        (by have := Nat.div_le_self (i' % (k + 1)) (2 ^ (s - 1)); omega)
      rw [heq] at e1
      have hJ := e1.1.symm.trans e2.1
      have hmod := Nat.ModEq.add_right_cancel' (q - 1 + i' % (k + 1) / 2 ^ (s - 1) % 2)
        (show i / (k + 1) + (q - 1 + i' % (k + 1) / 2 ^ (s - 1) % 2) ≡
          i' / (k + 1) + (q - 1 + i' % (k + 1) / 2 ^ (s - 1) % 2) [MOD q] by
          unfold Nat.ModEq
          rw [← add_assoc, ← add_assoc]
          rw [show i / (k + 1) + q - 1 = i / (k + 1) + (q - 1) by omega,
            show i' / (k + 1) + q - 1 = i' / (k + 1) + (q - 1) by omega] at hJ
          exact hJ)
      unfold Nat.ModEq at hmod
      rwa [Nat.mod_eq_of_lt hji, Nat.mod_eq_of_lt hji'] at hmod
    · rcases Nat.mod_two_eq_zero_or_one (i % (k + 1) / 2 ^ (s - 1)) with h | h
      · have h' : (i' % (k + 1) / 2 ^ (s - 1)) % 2 = 1 := by omega
        obtain ⟨d, hd1, hd2, hd⟩ := hcross i' i hi' hi (s - 1) h' h heq.symm
        exact ⟨d, hd1, hd2, Or.inr hd⟩
      · have h' : (i' % (k + 1) / 2 ^ (s - 1)) % 2 = 0 := by omega
        obtain ⟨d, hd1, hd2, hd⟩ := hcross i i' hi hi' (s - 1) h h' heq
        exact ⟨d, hd1, hd2, Or.inl hd⟩


/-- Vertices at forward distance `d ∈ [1, k]` share a label. -/
theorem simple_graph_equivalence_covering_number_cycle_power_dvd_complete (k q L : ℕ)
    (hq : 2 ≤ q) (hL : k + 1 ≤ 2 ^ L) (i i' d : ℕ) (hi : i < q * (k + 1))
    (hi' : i' < q * (k + 1)) (hd1 : 1 ≤ d) (hdk : d ≤ k) (h : (i + d) % (q * (k + 1)) = i') :
    ∃ s, s < 1 + L ∧
      (if s = 0 then i / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i) =
      (if s = 0 then i' / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i') := by
  have hK : 0 < k + 1 := by omega
  have hq0 : 0 < q := by omega
  have hdi := Nat.div_add_mod' i (k + 1)
  have hmi := Nat.mod_lt i hK
  have hj0 := Nat.zero_le (i / (k + 1))
  have hn2 : 2 * (k + 1) ≤ q * (k + 1) := Nat.mul_le_mul_right _ hq
  have hji : i / (k + 1) < q := (Nat.div_lt_iff_lt_mul hK).mpr hi
  have hmul : (i / (k + 1) + 1) * (k + 1) = i / (k + 1) * (k + 1) + (k + 1) := by ring
  have hsame : i' / (k + 1) = i / (k + 1) → ∃ s, s < 1 + L ∧
      (if s = 0 then i / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i) =
      (if s = 0 then i' / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i') := by
    intro hj
    exact ⟨0, by omega, by simp [hj]⟩
  have hcross : ∀ j' a', i' / (k + 1) = j' → i' % (k + 1) = a' → a' < i % (k + 1) →
      (j' = i / (k + 1) + 1 ∨ (i / (k + 1) = q - 1 ∧ j' = 0)) → ∃ s, s < 1 + L ∧
      (if s = 0 then i / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i) =
      (if s = 0 then i' / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s - 1) i') := by
    intro j' a' hj' ha' hlt hcase
    obtain ⟨ℓ, hℓ, p, hp1, hp2⟩ := simple_graph_equivalence_covering_number_cycle_power_dvd_bits L
      (i % (k + 1)) a' hlt (by omega)
    refine ⟨ℓ + 1, by omega, ?_⟩
    simp only [show ℓ + 1 ≠ 0 by omega, if_false, show ℓ + 1 - 1 = ℓ by omega]
    unfold simple_graph_equivalence_covering_number_cycle_power_dvd_lab
    rw [hp1, hj', ha', hp2, show (2 * p + 1) % 2 = 1 by omega, show (2 * p + 1) / 2 = p by omega,
      show 2 * p % 2 = 0 by omega, show 2 * p / 2 = p by omega]
    congr 2
    rw [show i / (k + 1) + q - 1 + 1 = i / (k + 1) + q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hji]
    rcases hcase with hc | ⟨hc1, hc2⟩
    · rw [hc, show i / (k + 1) + 1 + q - 1 + 0 = i / (k + 1) + q by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hji]
    · rw [hc2, hc1, show 0 + q - 1 + 0 = q - 1 by omega, Nat.mod_eq_of_lt (by omega)]
  by_cases hwrap : i + d < q * (k + 1)
  · rw [Nat.mod_eq_of_lt hwrap] at h
    by_cases hsm : i % (k + 1) + d < k + 1
    · apply hsame
      have e := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        (i / (k + 1)) (i % (k + 1) + d) hK hsm
      rw [show i / (k + 1) * (k + 1) + (i % (k + 1) + d) = i' by omega] at e
      exact e.1
    · have e := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
        (i / (k + 1) + 1) (i % (k + 1) + d - (k + 1)) hK (by omega)
      rw [show (i / (k + 1) + 1) * (k + 1) + (i % (k + 1) + d - (k + 1)) = i' by omega] at e
      exact hcross _ _ e.1 e.2 (by omega) (Or.inl rfl)
  · have h' : i' = i + d - q * (k + 1) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
      exact h.symm
    have hlast : i / (k + 1) = q - 1 := by
      by_contra hc
      have hle : i / (k + 1) + 1 + 1 ≤ q := by omega
      have := Nat.mul_le_mul_right (k + 1) hle
      rw [Nat.succ_mul] at this
      omega
    have hqK : (q - 1) * (k + 1) + (k + 1) = q * (k + 1) := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [hlast] at hdi
    have e := simple_graph_equivalence_covering_number_cycle_power_dvd_decode (k + 1)
      0 i' hK (by omega)
    rw [zero_mul, zero_add] at e
    exact hcross 0 i' e.1 e.2 (by omega) (Or.inr ⟨hlast, rfl⟩)

/-- Forward distance `d ∈ [1, k]` in values gives adjacency in `C_n^k`. -/
theorem simple_graph_equivalence_covering_number_cycle_power_dvd_adj (n k : ℕ) [NeZero n]
    (u v : ZMod n) (d : ℕ) (hd1 : 1 ≤ d) (hdk : d ≤ k) (hdn : d < n)
    (h : (u.val + d) % n = v.val) : (simple_graph_cycle_power n k).Adj u v := by
  have hv : v = u + (d : ZMod n) := by
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_cast_of_lt hdn]
    exact h.symm
  rw [hv]
  exact simple_graph_equivalence_covering_number_cycle_power_ge_adj n k u d hd1 hdk hdn

/-- The cover of `C_{q(k+1)}^k` by `1 + ⌈log₂(k+1)⌉` equivalence subgraphs: the blocks of
`k + 1` consecutive vertices, and one subgraph per binary digit. -/
theorem simple_graph_equivalence_covering_number_cycle_power_dvd_cover (k q : ℕ) (hk : 1 ≤ k)
    (hq : 2 ≤ q) :
    simple_graph_has_equivalence_cover (simple_graph_cycle_power (q * (k + 1)) k)
      (1 + Nat.clog 2 (k + 1)) := by
  classical
  have : NeZero (q * (k + 1)) := ⟨by positivity⟩
  have hK : 0 < k + 1 := by omega
  have hq0 : 0 < q := by omega
  have hn : 2 * k + 2 ≤ q * (k + 1) := by nlinarith
  refine ⟨fun s v => (((if s.val = 0 then v.val / (k + 1) * (k + 1)
    else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s.val - 1)
      v.val) : ℕ) : ZMod (q * (k + 1))), ?_, ?_⟩
  · intro s u v huv h
    have hb : ∀ w : ZMod (q * (k + 1)), (if s.val = 0 then w.val / (k + 1) * (k + 1)
        else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s.val - 1)
          w.val) < q * (k + 1) := by
      intro w
      have hw := ZMod.val_lt w
      split_ifs
      · exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw
      · unfold simple_graph_equivalence_covering_number_cycle_power_dvd_lab
        have hJ := Nat.mod_lt (w.val / (k + 1) + q - 1 + w.val % (k + 1) / 2 ^ (s.val - 1) % 2) hq0
        have hD := Nat.div_le_self (w.val % (k + 1)) (2 ^ (s.val - 1))
        have hm := Nat.mod_lt w.val hK
        have hle := Nat.mul_le_mul_right (k + 1) (show
          (w.val / (k + 1) + q - 1 + w.val % (k + 1) / 2 ^ (s.val - 1) % 2) % q + 1 ≤ q from hJ)
        rw [Nat.succ_mul] at hle
        omega
    have hnat := congrArg ZMod.val h
    simp only at hnat
    rw [ZMod.val_cast_of_lt (hb u), ZMod.val_cast_of_lt (hb v)] at hnat
    have hne : u.val ≠ v.val := fun h' => huv (ZMod.val_injective _ h')
    obtain ⟨d, hd1, hd2, hd⟩ := simple_graph_equivalence_covering_number_cycle_power_dvd_sound
      k q hq u.val v.val (ZMod.val_lt u) (ZMod.val_lt v) hne s.val hnat
    rcases hd with hd | hd
    · exact simple_graph_equivalence_covering_number_cycle_power_dvd_adj _ k u v d hd1 hd2
        (by omega) hd
    · exact (simple_graph_equivalence_covering_number_cycle_power_dvd_adj _ k v u d hd1 hd2
        (by omega) hd).symm
  · have hL : k + 1 ≤ 2 ^ Nat.clog 2 (k + 1) := Nat.le_pow_clog (by norm_num) _
    have key : ∀ u v : ZMod (q * (k + 1)), u ≠ v → (v - u).val ≤ k → ∃ s : Fin (1 + Nat.clog 2 (k + 1)),
        (((if s.val = 0 then u.val / (k + 1) * (k + 1)
          else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s.val - 1)
            u.val) : ℕ) : ZMod (q * (k + 1))) =
        (((if s.val = 0 then v.val / (k + 1) * (k + 1)
          else simple_graph_equivalence_covering_number_cycle_power_dvd_lab q (k + 1) (s.val - 1)
            v.val) : ℕ) : ZMod (q * (k + 1))) := by
      intro u v hne hle
      have hd1 : 1 ≤ (v - u).val := by
        rcases Nat.eq_zero_or_pos (v - u).val with h0 | h0
        · rw [ZMod.val_eq_zero, sub_eq_zero] at h0
          exact absurd h0.symm hne
        · exact h0
      have hmod : (u.val + (v - u).val) % (q * (k + 1)) = v.val := by
        rw [← ZMod.val_add, add_sub_cancel]
      obtain ⟨s, hs, heq⟩ := simple_graph_equivalence_covering_number_cycle_power_dvd_complete
        k q (Nat.clog 2 (k + 1)) hq hL u.val v.val (v - u).val (ZMod.val_lt u) (ZMod.val_lt v)
        hd1 hle hmod
      exact ⟨⟨s, hs⟩, by simp only; rw [heq]⟩
    intro u v huv
    obtain ⟨hne, hmin⟩ := huv
    rcases min_le_iff.mp hmin with h | h
    · obtain ⟨s, hs⟩ := key v u (Ne.symm hne) h
      exact ⟨s, hs.symm⟩
    · exact key u v hne h

theorem simple_graph_equivalence_covering_number_cycle_power_dvd (k q : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power (q * (k + 1)) k) =
      1 + Nat.clog 2 (k + 1) := by
  apply le_antisymm
  · unfold simple_graph_equivalence_covering_number
    exact Nat.sInf_le (simple_graph_equivalence_covering_number_cycle_power_dvd_cover k q hk hq)
  · exact simple_graph_equivalence_covering_number_cycle_power_ge (q * (k + 1)) k hk
      (by nlinarith)
