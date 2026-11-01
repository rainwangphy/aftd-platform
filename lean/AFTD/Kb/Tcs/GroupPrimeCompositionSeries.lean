import AFTD.Prelude

/-!
# GroupPrimeCompositionSeries

Topic: data_structures   Node: 3d9d15789ae8

Provenance: formalization of a published result. Source: arXiv:2610.31363; OP-808

A prime composition series of length k for group G with prime quotient orders p : Fin k → ℕ is a chain of subgroups H_0 = ⊥ ≤ ... ≤ H_k = ⊤ such that each H_i is normal in H_{i+1} with prime index p_i.
-/

/-- A subnormal series from bot to top in a finite group G whose successive quotients are normal with prime orders p_i. -/
structure GroupPrimeCompositionSeries (G : Type*) [Group G] (k : ℕ) (p : Fin k → ℕ) where
  H : Fin (k + 1) → Subgroup G
  bot : H 0 = ⊥
  top : H (Fin.last k) = ⊤
  le : ∀ i : Fin k, H (Fin.castSucc i) ≤ H (Fin.succ i)
  normal : ∀ i : Fin k, ((H (Fin.castSucc i)).subgroupOf (H (Fin.succ i))).Normal
  index_eq : ∀ i : Fin k, ((H (Fin.castSucc i)).subgroupOf (H (Fin.succ i))).index = p i
  prime : ∀ i : Fin k, Nat.Prime (p i)
