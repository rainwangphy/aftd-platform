import AFTD.Prelude

/-!
# op869_explicit_simulation_budgets

Topic: online_algorithms   Node: 94fc204a8c60

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.5

The per-copy and reservation bounds fit the simulation vertex and post-degree budgets with constant 10.
-/

/-- Numerical overhead for the online-coloring fold simulation. -/
theorem op869_explicit_simulation_budgets (K q D n t : ℕ)
    (hK : 1 ≤ K) (hq : 1 ≤ q) (hD : 1 ≤ D) :
    let r := (q+t-1)/t
    let B := K*2^(5*r)
    let R := K*q*D
    n*R*B ≤ 10*K^2*q*n*D*2^(10*r) ∧
    R*B+B ≤ 10*K^2*q*D*2^(10*r) := by
  dsimp only
  let r := (q+t-1)/t
  let B := K*2^(5*r)
  let R := K*q*D
  change n*R*B ≤ 10*K^2*q*n*D*2^(10*r) ∧ R*B+B ≤ 10*K^2*q*D*2^(10*r)
  have hKpos : 0 < K := by omega
  have hqpos : 0 < q := by omega
  have hDpos : 0 < D := by omega
  have hR : 1 ≤ R := by
    have hrpos : 0 < R := by dsimp [R]; positivity
    omega
  have hE : 2^(5*r) ≤ 2^(10*r) := Nat.pow_le_pow_right (by omega) (by omega)
  have hB : B ≤ R*B := by simpa using Nat.mul_le_mul_right B hR
  constructor
  · calc
      n*R*B = K^2*q*n*D*2^(5*r) := by dsimp [R,B]; ring
      _ ≤ 10*K^2*q*n*D*2^(10*r) := by gcongr <;> omega
  · calc
      R*B+B ≤ 2*(R*B) := by omega
      _ = 2*K^2*q*D*2^(5*r) := by dsimp [R,B]; ring
      _ ≤ 10*K^2*q*D*2^(10*r) := by gcongr <;> omega
