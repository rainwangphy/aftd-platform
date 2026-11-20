import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionFixedEndpoints
import AFTD.Kb.Tcs.Op874PathTwoPalettesAvoidEndpoint
import AFTD.Kb.Tcs.G

/-!
# single_defect_high_states_of_factor_word

Topic: graphs   Node: f583fddd2df9

Provenance: helper lemma. OP-874 one-defect path-palette reduction using the proved fixed-endpoint path selection lemma.

A proper cyclic factor word with compatible defect colors and an occurrence of the remaining defect color on an interior edge admits the required high-port choices.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace In1081HighPorts

def palette (a b : Fin 4) : Finset (Fin 4) := Finset.univ \ ({a,b} : Finset (Fin 4))

theorem palette_card (a b : Fin 4) (h : a ≠ b) : (palette a b).card = 2 := by
  fin_cases a <;> fin_cases b <;> simp_all [palette, Finset.card_sdiff]

theorem palette_mem (a b x : Fin 4) : x ∈ palette a b ↔ x ≠ a ∧ x ≠ b := by
  simp [palette]

theorem in1081_single_defect_high_states
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (c : Fin n → Fin 4) (t u : Fin 4)
    (hc : ∀ i, c (i - 1) ≠ c i) (htu : t ≠ u)
    (ht0 : t ≠ c 0) (htlast : t ≠ c (-1)) (hu0 : u ≠ c 0)
    (hulast : u ≠ c (-1)) (hfirst : c 1 ≠ c (-1))
    (hint : ∃ i : Fin n, i ≠ 0 ∧ i + 1 ≠ 0 ∧ c i = u) :
    ∃ p q : Fin n → Fin 4,
      (∀ i, p i ≠ q i ∧ p i ≠ c (i-1) ∧ p i ≠ c i ∧
        q i ≠ c (i-1) ∧ q i ≠ c i) ∧
      p 0 = t ∧ q 0 = u ∧ q 1 = c (-1) ∧ p (-1) ≠ q 0 ∧
      (∀ i, i ≠ 0 → i+1 ≠ 0 → p i ≠ q (i+1)) := by
  classical
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hlast : (-1 : Fin n).val = n-1 := by
    rw [Fin.val_neg', hone, Nat.mod_eq_of_lt (by omega : n-1 < n)]
  have h1ne : (1 : Fin n) ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    rw [hone] at hh
    change 1 = 0 at hh
    omega
  let v : ℕ → Fin n := fun i => Fin.ofNat n (i+1)
  let P : ℕ → Finset (Fin 4) := fun i => palette (c (v i-1)) (c (v i))
  have hcard : ∀ i, (P i).card = 2 := by
    intro i
    exact palette_card _ _ (hc (v i))
  have hv0 : v 0 = 1 := by
    apply Fin.ext
    simp [v, Fin.val_ofNat, hone, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hvlast : v (n-2) = -1 := by
    apply Fin.ext
    rw [hlast]
    simp only [v, Fin.val_ofNat]
    have he : n-2+1=n-1 := by omega
    rw [he, Nat.mod_eq_of_lt (by omega : n-1 < n)]
  have hx : c (-1) ∈ P 0 := by
    apply (palette_mem _ _ _).mpr
    rw [show v 0 = 1 from hv0]
    constructor
    · have h := hc (0 : Fin n)
      simpa using h
    · exact hfirst.symm
  have hmissing : ∃ k ≤ n-2, u ∉ P k := by
    obtain ⟨i, hi0, hi1, hiu⟩ := hint
    have hilow : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := by
        intro h
        apply hi0
        apply Fin.ext
        exact h
      omega
    have hihigh : i.val < n-1 := by
      have hi := i.isLt
      by_contra h
      have hv : i.val = n-1 := by omega
      apply hi1
      apply Fin.ext
      rw [Fin.val_add, hone, hv]
      change (n-1+1)%n = 0
      have he : n-1+1=n := by omega
      rw [he, Nat.mod_self]
    let k := i.val-1
    have hk : k ≤ n-2 := by dsimp [k]; omega
    have hvk : v k = i := by
      apply Fin.ext
      simp only [v, Fin.val_ofNat]
      have he : k+1 = i.val := by dsimp [k]; omega
      rw [he, Nat.mod_eq_of_lt i.isLt]
    refine ⟨k, hk, ?_⟩
    rw [show P k = palette (c (v k-1)) (c (v k)) from rfl, palette_mem]
    intro h
    exact h.2 (by simpa [hvk] using hiu.symm)
  obtain ⟨f,g,hf0,hglast,hpal,hstep⟩ :=
    op874_path_two_palettes_avoid_endpoint P hcard (n-2) (c (-1)) u hx hmissing
  let p : Fin n → Fin 4 := fun i => if i = 0 then t else g (i.val-1)
  let q : Fin n → Fin 4 := fun i => if i = 0 then u else f (i.val-1)
  have hvindex (i : Fin n) (hi : i ≠ 0) : v (i.val-1) = i := by
    have hilow : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      omega
    apply Fin.ext
    simp only [v, Fin.val_ofNat]
    have he : i.val-1+1=i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]
  refine ⟨p,q,?_,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i=0
    · subst i
      simp only [p,q,if_pos rfl, zero_sub]
      exact ⟨htu,htlast,ht0,hulast,hu0⟩
    · have hilow : 1 ≤ i.val := by
        have hv : i.val ≠ 0 := by
          intro h
          apply hi
          apply Fin.ext
          exact h
        omega
      have hk : i.val-1 ≤ n-2 := by have := i.isLt; omega
      obtain ⟨hf,hg,hfg⟩ := hpal (i.val-1) hk
      have hp := (palette_mem _ _ _).mp (show g (i.val-1) ∈ palette (c (v (i.val-1)-1)) (c (v (i.val-1))) from hg)
      have hq := (palette_mem _ _ _).mp (show f (i.val-1) ∈ palette (c (v (i.val-1)-1)) (c (v (i.val-1))) from hf)
      rw [hvindex i hi] at hp hq
      simp only [p,q,if_neg hi]
      exact ⟨hfg.symm,hp.1,hp.2,hq.1,hq.2⟩
  · simp [p]
  · simp [q]
  · have heq : q 1 = f 0 := by
      change (if (1 : Fin n) = 0 then u else f ((1 : Fin n).val-1)) = f 0
      rw [if_neg h1ne, hone]
    exact heq.trans hf0
  · have hlastne : (-1 : Fin n) ≠ 0 := by
      intro h
      have hh := congrArg Fin.val h
      simp [hlast] at hh
      omega
    simp only [p,q,if_pos rfl,if_neg hlastne,hlast]
    exact hglast
  · intro i hi hi1
    have hilow : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := by
        intro h
        apply hi
        apply Fin.ext
        exact h
      omega
    have hnext : i.val+1 < n := by
      by_contra h
      have he : i.val+1=n := by have := i.isLt; omega
      apply hi1
      apply Fin.ext
      rw [Fin.val_add,hone,he]
      simp
    have hvnext : (i+1).val = i.val+1 := by
      rw [Fin.val_add,hone,Nat.mod_eq_of_lt hnext]
    simp only [p,q,if_neg hi,if_neg hi1,hvnext]
    have hk : i.val-1 < n-2 := by omega
    have hs := hstep (i.val-1) hk
    have he : i.val-1+1=i.val := by omega
    simpa [he] using hs
end In1081HighPorts

theorem single_defect_high_states_of_factor_word (n : ℕ) [NeZero n] (hn : 3 ≤ n) (c : Fin n → Fin 4) (t u : Fin 4) (hc : ∀ i, c (i - 1) ≠ c i) (htu : t ≠ u) (ht0 : t ≠ c 0) (htlast : t ≠ c (-1)) (hu0 : u ≠ c 0) (hulast : u ≠ c (-1)) (hfirst : c 1 ≠ c (-1)) (hint : ∃ i : Fin n, i ≠ 0 ∧ i + 1 ≠ 0 ∧ c i = u) : ∃ p q : Fin n → Fin 4, (∀ i, p i ≠ q i ∧ p i ≠ c (i - 1) ∧ p i ≠ c i ∧ q i ≠ c (i - 1) ∧ q i ≠ c i) ∧ p 0 = t ∧ q 0 = u ∧ q 1 = c (-1) ∧ p (-1) ≠ q 0 ∧ (∀ i, i ≠ 0 → i + 1 ≠ 0 → p i ≠ q (i + 1)) := by
  exact In1081HighPorts.in1081_single_defect_high_states n hn c t u hc htu ht0 htlast hu0 hulast hfirst hint
