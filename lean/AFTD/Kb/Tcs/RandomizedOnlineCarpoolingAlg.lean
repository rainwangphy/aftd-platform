import AFTD.Prelude

/-!
# RandomizedOnlineCarpoolingAlg

Topic: online_algorithms   Node: 374e27566f7d

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 1.1, 3.1, Online carpooling against an oblivious adversary

A randomized online carpooling algorithm consists of a function num_coins : ℕ → ℕ → ℕ specifying the number of boolean coins for vertex count n and horizon T, and an online orientation function orient : (n : ℕ) → (T : ℕ) → List (Fin n × Fin n) → (Fin (num_coins n T) → Bool) → Bool that determines the orientation bit of the arriving edge given the edge history and the random coins.
-/

/-- A randomized online carpooling algorithm family parameterized by vertex count and horizon. -/
structure RandomizedOnlineCarpoolingAlg where
  num_coins : ℕ → ℕ → ℕ
  orient : (n : ℕ) → (T : ℕ) → List (Fin n × Fin n) → (Fin (num_coins n T) → Bool) → Bool
