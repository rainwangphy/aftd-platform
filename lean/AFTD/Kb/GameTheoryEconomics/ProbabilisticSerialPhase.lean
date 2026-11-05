import AFTD.Prelude

/-!
# probabilistic_serial_phase

Topic: social_choice   Node: 880acae7557e

Provenance: helper lemma. arXiv:2611.05777 (Sublinear Metric Distortion for Matching), Sec. 1 and Sec. 6: one-sided matching of n agents to n items with ordinal rankings by distance; the probabilistic serial rule; one phase of the eating procedure, helper for probabilistic_serial_fractional_assignment

One phase of the simultaneous-eating (probabilistic serial) procedure for n agents and n items. Agent i's ranking is the permutation pref i, with pref i k its k-th favourite item. Given remaining capacities r_j and consumed amounts X_ij, agent i eats item j in this phase iff r_j > 0 and j has the smallest rank (pref i)^{-1}(j) among items with positive remaining capacity. With c_j the number of agents eating j, the phase lasts t = min over items with c_j > 0 of r_j / c_j (t = 0 if no item is eaten); then r_j becomes r_j - t c_j and X_ij increases by t if agent i eats j.
-/

/-- One phase of probabilistic serial (simultaneous eating). `pref i k` is agent `i`'s `k`-th favourite item; the state `s` is (remaining capacity of each item, amount of each item eaten so far by each agent). Every agent eats her favourite item with positive remaining capacity, at unit speed, until the first such item runs out. -/
noncomputable def probabilistic_serial_phase (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
  open Classical in
  let eats : Fin n → Fin n → Prop := fun i j =>
    0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j'
  let cnt : Fin n → ℕ := fun j => (Finset.univ.filter (fun i => eats i j)).card
  let S := Finset.univ.filter (fun j => 0 < cnt j)
  let t : ℝ := if h : S.Nonempty then S.inf' h (fun j => s.1 j / cnt j) else 0
  (fun j => s.1 j - t * cnt j, fun i j => s.2 i j + if eats i j then t else 0)
