import AFTD.Prelude

/-!
# is_hare_valid_assignment

Topic: social_choice   Node: d1f8be3c1fc8

A Hare-valid Monroe assignment (arXiv:2508.00811, Def. 16): W has k members, π sends every voter into W, and every c ∈ W receives between ⌊n/k⌋ and ⌈n/k⌉ voters.
-/

/-- A Hare-valid Monroe assignment (arXiv:2508.00811, Def. 16): `W` has `k` members, `π` sends every voter into `W`, and every `c ∈ W` gets between `⌊n/k⌋` and `⌈n/k⌉` voters. -/
def is_hare_valid_assignment {n m : ℕ} (k : ℕ) (W : Finset (Fin m)) (π : Fin n → Fin m) : Prop :=
  W.card = k ∧ (∀ i, π i ∈ W) ∧
    ∀ c ∈ W, n / k ≤ (Finset.univ.filter fun i => π i = c).card ∧
      (Finset.univ.filter fun i => π i = c).card ≤ (n + k - 1) / k
