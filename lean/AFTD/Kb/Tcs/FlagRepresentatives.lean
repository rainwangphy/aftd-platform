import AFTD.Prelude
import AFTD.Kb.Tcs.GroupPrimeCompositionSeries

/-!
# FlagRepresentatives

Topic: data_structures   Node: 043c3aca3ec2

Provenance: formalization of a published result. Source: arXiv:2610.31363; OP-808

For a prime composition series series, FlagRepresentatives bundles a family of group elements g : (i : Fin k) → Fin (p i) → G such that for each step i : Fin k and d : Fin (p i), g i d belongs to series.H (Fin.succ i), g i 0 = 1, g i 1 does not belong to series.H (Fin.castSucc i), and ((g i 1)^d.val)⁻¹ * g i d belongs to series.H (Fin.castSucc i).
-/

/-- Coset representatives for each step of a prime composition series whose cosets are successive powers of g_{i,1}. -/
structure FlagRepresentatives {G : Type*} [Group G] {k : ℕ} {p : Fin k → ℕ}
    (series : GroupPrimeCompositionSeries G k p) where
  g : (i : Fin k) → Fin (p i) → G
  mem : ∀ (i : Fin k) (d : Fin (p i)), g i d ∈ series.H (Fin.succ i)
  zero : ∀ (i : Fin k), g i ⟨0, (series.prime i).pos⟩ = 1
  not_mem_one : ∀ (i : Fin k), g i ⟨1, (series.prime i).one_lt⟩ ∉ series.H (Fin.castSucc i)
  coset_pow : ∀ (i : Fin k) (d : Fin (p i)),
    ((g i ⟨1, (series.prime i).one_lt⟩)^d.val)⁻¹ * g i d ∈ series.H (Fin.castSucc i)
