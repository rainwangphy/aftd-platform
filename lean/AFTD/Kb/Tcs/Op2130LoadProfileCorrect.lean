import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130LoadSpatialCorrect

/-!
# op2130_load_profile_correct

Topic: online_algorithms   Node: 077f8fa9ebc9

Provenance: helper lemma. OP-2130, all-size prepared decision-circuit loading

For any number of gates and any bits and dummy coins, the reverse loading procedure transforms the prepared profile into the invariant with every gate and bit correctly encoded while preserving the boundary references.
-/

set_option maxHeartbeats 1000000
def op2130_load_inv (N k : ℕ) (h : ℕ → ℤ) (bits : ℕ → Bool) : Prop :=
  h 0 = 0 ∧ h 1 = -3 ∧
  h (2+2*N) = (if N%2=0 then -1 else 2) ∧
  (∀ j, j < k → h (2+2*j) = if j%2=0 then 0 else 1) ∧
  (∀ j, j < k → h (3+2*j) = if j%2=0 then 5 else -3) ∧
  (∀ j, k ≤ j → j < N → h (2+2*j) = if j%2=0 then -1 else 2) ∧
  (∀ j, k ≤ j → j < N → h (3+2*j) =
    if j%2=0 then (if bits j then 2 else 0) else (if bits j then 1 else -1))

def op2130_load_at (h : ℕ → ℤ) (i : ℕ) (bits coins : ℕ → Bool) : ℕ → ℤ :=
  if i%2=0 then op2130_load_even_spatial h (2+2*i) (bits i)
    (coins (5*i)) (coins (5*i+1)) (coins (5*i+2)) (coins (5*i+3)) (coins (5*i+4))
  else op2130_load_odd_spatial h (2+2*i) (bits i)
    (coins (5*i)) (coins (5*i+1)) (coins (5*i+2)) (coins (5*i+4))

theorem op2130_load_inv_step (N j : ℕ) (h : ℕ → ℤ) (bits coins : ℕ → Bool)
    (hj : j < N) (hinv : op2130_load_inv N (j+1) h bits) :
    op2130_load_inv N j (op2130_load_at h j bits coins) bits := by
  rcases hinv with ⟨hz,href,hsentinel,hgate0,hbit0,hgate1,hbit1⟩
  let p := 2+2*j
  have hgate : h p = if j%2=0 then 0 else 1 := hgate0 j (by omega)
  have hbit : h (p+1) = if j%2=0 then 5 else -3 := by
    have hh := hbit0 j (by omega)
    simpa [p,show 3+2*j=(2+2*j)+1 by omega] using hh
  have hleft : h (p-1) = if j%2=0 then -3 else 5 := by
    by_cases hzero : j=0
    · subst j
      simpa [p] using href
    · have hh := hbit0 (j-1) (by omega)
      have hidx : 3+2*(j-1) = p-1 := by dsimp [p]; omega
      rw [hidx] at hh
      by_cases he : j%2=0
      · have ho : (j-1)%2 ≠ 0 := by omega
        simpa [he,ho] using hh
      · have he' : (j-1)%2 = 0 := by omega
        simpa [he,he'] using hh
  have hright : h (p+2) = if j%2=0 then 2 else -1 := by
    have hidx : 2+2*(j+1)=p+2 := by dsimp [p]; omega
    by_cases hn : j+1=N
    · rw [hn] at hidx
      rw [← hidx, hsentinel, ← hn]
      by_cases he : j%2=0
      · simp [he,show (j+1)%2 ≠ 0 by omega]
      · simp [he,show (j+1)%2 = 0 by omega]
    · have hj1 : j+1<N := by omega
      have hh := hgate1 (j+1) (by omega) hj1
      rw [hidx] at hh
      by_cases he : j%2=0
      · have ho : (j+1)%2 ≠ 0 := by omega
        simpa [he,ho] using hh
      · have he' : (j+1)%2 = 0 := by omega
        simpa [he,he'] using hh
  let out := op2130_load_at h j bits coins
  have hlocal : out p = (if j%2=0 then -1 else 2) ∧
      out (p+1) = (if j%2=0 then (if bits j then 2 else 0) else (if bits j then 1 else -1)) ∧
      ∀ k, k ≠ p → k ≠ p+1 → out k = h k := by
    by_cases he : j%2=0
    · have hh := op2130_load_even_spatial_correct h p (by dsimp [p]; omega) (bits j)
        (coins (5*j)) (coins (5*j+1)) (coins (5*j+2)) (coins (5*j+3)) (coins (5*j+4))
        (by simpa [he] using hleft) (by simpa [he] using hgate)
        (by simpa [he] using hbit) (by simpa [he] using hright)
      simpa [out,op2130_load_at,he,p] using hh
    · have hh := op2130_load_odd_spatial_correct h p (by dsimp [p]; omega) (bits j)
        (coins (5*j)) (coins (5*j+1)) (coins (5*j+2)) (coins (5*j+4))
        (by simpa [he] using hleft) (by simpa [he] using hgate)
        (by simpa [he] using hbit) (by simpa [he] using hright)
      simpa [out,op2130_load_at,he,p] using hh
  change op2130_load_inv N j out bits
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hlocal.2.2 0 (by dsimp [p]; omega) (by dsimp [p]; omega),hz]
  · rw [hlocal.2.2 1 (by dsimp [p]; omega) (by dsimp [p]; omega),href]
  · rw [hlocal.2.2 (2+2*N) (by dsimp [p]; omega) (by dsimp [p]; omega),hsentinel]
  · intro i hi
    rw [hlocal.2.2 (2+2*i) (by dsimp [p]; omega) (by dsimp [p]; omega)]
    exact hgate0 i (by omega)
  · intro i hi
    rw [hlocal.2.2 (3+2*i) (by dsimp [p]; omega) (by dsimp [p]; omega)]
    exact hbit0 i (by omega)
  · intro i hi hiN
    by_cases heq : i=j
    · subst i
      exact hlocal.1
    · rw [hlocal.2.2 (2+2*i) (by dsimp [p]; omega) (by dsimp [p]; omega)]
      exact hgate1 i (by omega) hiN
  · intro i hi hiN
    by_cases heq : i=j
    · subst i
      simpa [p,show 3+2*j=(2+2*j)+1 by omega] using hlocal.2.1
    · rw [hlocal.2.2 (3+2*i) (by dsimp [p]; omega) (by dsimp [p]; omega)]
      exact hbit1 i (by omega) hiN

def op2130_load_reverse (bits coins : ℕ → Bool) : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, h => h
  | k+1, h => op2130_load_reverse bits coins k (op2130_load_at h k bits coins)

theorem op2130_load_inv_induction (N k : ℕ) (h : ℕ → ℤ) (bits coins : ℕ → Bool)
    (hk : k ≤ N) (hinv : op2130_load_inv N k h bits) :
    op2130_load_inv N 0 (op2130_load_reverse bits coins k h) bits := by
  induction k generalizing h with
  | zero => simpa [op2130_load_reverse] using hinv
  | succ k ih =>
      rw [op2130_load_reverse]
      apply ih (op2130_load_at h k bits coins) (by omega)
      exact op2130_load_inv_step N k h bits coins (by omega) hinv

def op2130_load_profile (N j : ℕ) : ℤ :=
  if j = 1 then -3
  else if 2 ≤ j ∧ j ≤ 2+2*N then
    if j%2=0 then
      let i := (j-2)/2
      if i=N then (if N%2=0 then -1 else 2) else if i%2=0 then 0 else 1
    else let i := (j-3)/2; if i%2=0 then 5 else -3
  else 0

theorem op2130_load_profile_initial (N : ℕ) (bits : ℕ → Bool) :
    op2130_load_inv N N (op2130_load_profile N) bits := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp [op2130_load_profile]
  · simp [op2130_load_profile]
  · simp only [op2130_load_profile,show 2+2*N ≠ 1 by omega, if_false, true_and,
      show 2 ≤ 2+2*N ∧ 2+2*N ≤ 2+2*N by omega, if_true,
      show (2+2*N)%2=0 by omega, show (2+2*N-2)/2=N by omega]
  · intro j hj
    simp only [op2130_load_profile,show 2+2*j ≠ 1 by omega, if_false, true_and,
      show 2 ≤ 2+2*j ∧ 2+2*j ≤ 2+2*N by omega, if_true,
      show (2+2*j)%2=0 by omega, show (2+2*j-2)/2=j by omega,
      show j ≠ N by omega]
  · intro j hj
    simp only [op2130_load_profile,show 3+2*j ≠ 1 by omega, if_false, true_and,
      show 2 ≤ 3+2*j ∧ 3+2*j ≤ 2+2*N by omega, if_true,
      show (3+2*j)%2 ≠ 0 by omega, show (3+2*j-3)/2=j by omega]
  · intro j hj hjN
    omega
  · intro j hj hjN
    omega

theorem op2130_load_profile_correct (N : ℕ) (bits coins : ℕ → Bool) :
    op2130_load_inv N 0 (op2130_load_reverse bits coins N (op2130_load_profile N)) bits := by
  exact op2130_load_inv_induction N N (op2130_load_profile N) bits coins (by omega)
    (op2130_load_profile_initial N bits)
