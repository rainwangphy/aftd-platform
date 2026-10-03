import AFTD.Prelude

/-!
# is_droop_valid_assignment

Topic: social_choice   Node: 5162717430fc

A Droop-valid Monroe assignment (Casey–Elkind, Def. 16): |W| = k, each voter goes to a member of W or to the dummy (none), each c ∈ W gets between ⌊n/(k+1)⌋ and ⌈n/(k+1)⌉ voters and the dummy exactly ⌊n/(k+1)⌋.
-/

/-- A Droop-valid Monroe assignment (Casey–Elkind, Def. 16): `W` has `k` members, `π` sends each voter to a member of `W` or to the dummy `none`, every `c ∈ W` gets between `⌊n/(k+1)⌋` and `⌈n/(k+1)⌉` voters, and the dummy gets exactly `⌊n/(k+1)⌋`. -/
def is_droop_valid_assignment {n m : ℕ} (k : ℕ) (W : Finset (Fin m))
    (π : Fin n → Option (Fin m)) : Prop :=
  W.card = k ∧ (∀ i c, π i = some c → c ∈ W) ∧
    (∀ c ∈ W, n / (k + 1) ≤ (Finset.univ.filter fun i => π i = some c).card ∧
      (Finset.univ.filter fun i => π i = some c).card ≤ (n + k) / (k + 1)) ∧
    (Finset.univ.filter fun i => π i = none).card = n / (k + 1)
