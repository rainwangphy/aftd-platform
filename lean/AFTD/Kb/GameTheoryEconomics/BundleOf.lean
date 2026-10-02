import AFTD.Prelude

/-!
# bundle_of

Topic: fair_division   Node: a91d661521f7

Under an allocation that gives each item x to agent s(x), agent i's bundle is the set of items given to i.
-/

/-- The bundle of agent `i` under the allocation `σ` that gives item `x` to agent `σ x`. -/
def bundle_of {m n : ℕ} (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun x => σ x = i
