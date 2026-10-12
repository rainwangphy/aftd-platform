import AFTD.Prelude
import AFTD.Kb.Tcs.SavitchMidpoint
import AFTD.Kb.Tcs.SavitchMidpointMono

/-!
# savitch_depth_topological_potential_bound

Topic: space_complexity   Node: f98f38aa6c15

Provenance: original. Related work: Savitch 1970; Sipser, Theorem 8.5

Let V be a type, r a relation on V, and ℓ : V → ℕ a topological potential such that r u v implies ℓ u < ℓ v. For any vertices s, t with ℓ t - ℓ s ≤ D, and any k with D ≤ 2^k, if t is reachable from s under the reflexive-transitive closure of r, then the Savitch midpoint relation SavitchMidpoint r k s t holds.
-/

inductive savitch_depth_topological_potential_bound_reach {V : Type*} (r : V → V → Prop) :
    ℕ → V → V → Prop where
  | refl (u : V) : savitch_depth_topological_potential_bound_reach r 0 u u
  | tail {n : ℕ} {u v w : V} :
      savitch_depth_topological_potential_bound_reach r n u v → r v w →
      savitch_depth_topological_potential_bound_reach r (n + 1) u w

lemma savitch_depth_topological_potential_bound_zero {V : Type*} {r : V → V → Prop} {s t : V}
    (h : savitch_depth_topological_potential_bound_reach r 0 s t) : s = t := by
  cases h
  rfl

lemma savitch_depth_topological_potential_bound_one {V : Type*} {r : V → V → Prop} {s t : V}
    (h : savitch_depth_topological_potential_bound_reach r 1 s t) : r s t := by
  cases h with
  | tail h1 h2 =>
    cases h1
    exact h2

lemma savitch_depth_topological_potential_bound_of_reflTransGen {V : Type*} {r : V → V → Prop}
    {s t : V} (h : Relation.ReflTransGen r s t) :
    ∃ n, savitch_depth_topological_potential_bound_reach r n s t := by
  induction h with
  | refl => exact ⟨0, .refl s⟩
  | tail hab hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .tail hn hbc⟩

lemma savitch_depth_topological_potential_bound_pot {V : Type*} {r : V → V → Prop}
    {ℓ : V → ℕ} (hℓ : ∀ u v, r u v → ℓ u < ℓ v) {s t : V} {n : ℕ}
    (h : savitch_depth_topological_potential_bound_reach r n s t) : ℓ s + n ≤ ℓ t := by
  induction h with
  | refl u => exact Nat.le_refl _
  | tail h_uv h_vw ih =>
    have hlt := hℓ _ _ h_vw
    omega

lemma savitch_depth_topological_potential_bound_split {V : Type*} {r : V → V → Prop}
    {s t : V} {n : ℕ} (h : savitch_depth_topological_potential_bound_reach r n s t)
    (m : ℕ) (hm : m ≤ n) :
    ∃ w, savitch_depth_topological_potential_bound_reach r m s w ∧
      savitch_depth_topological_potential_bound_reach r (n - m) w t := by
  induction h generalizing m with
  | refl u =>
    have : m = 0 := by omega
    subst this
    exact ⟨u, .refl u, .refl u⟩
  | @tail n' u v w h_uv h_vw ih =>
    by_cases hle : m ≤ n'
    · obtain ⟨w', hw1, hw2⟩ := ih m hle
      refine ⟨w', hw1, ?_⟩
      have : n' + 1 - m = (n' - m) + 1 := by omega
      rw [this]
      exact .tail hw2 h_vw
    · have heq : m = n' + 1 := by omega
      subst heq
      have : n' + 1 - (n' + 1) = 0 := by omega
      rw [this]
      exact ⟨w, .tail h_uv h_vw, .refl w⟩

lemma savitch_depth_topological_potential_bound_midpoint {V : Type*} {r : V → V → Prop}
    (k : ℕ) {s t : V} {n : ℕ} (hn : n ≤ 2 ^ k)
    (h : savitch_depth_topological_potential_bound_reach r n s t) :
    SavitchMidpoint r k s t := by
  induction k generalizing s t n with
  | zero =>
    have : n ≤ 1 := hn
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · left
      exact savitch_depth_topological_potential_bound_zero h
    · right
      exact savitch_depth_topological_potential_bound_one h
  | succ k ih =>
    let m := min n (2 ^ k)
    have hm : m ≤ n := Nat.min_le_left _ _
    obtain ⟨w, hw1, hw2⟩ := savitch_depth_topological_potential_bound_split h m hm
    refine ⟨w, ih ?_ hw1, ih ?_ hw2⟩
    · exact Nat.min_le_right _ _
    · rw [Nat.pow_succ] at hn
      omega

/-- Savitch midpoint depth bound on ranked DAGs: reachability is certified at depth k whenever the topological potential span D satisfies D ≤ 2^k. -/
theorem savitch_depth_topological_potential_bound {V : Type*} (r : V → V → Prop)
    (ℓ : V → ℕ) (hℓ : ∀ u v, r u v → ℓ u < ℓ v) {s t : V} (D k : ℕ)
    (hD : ℓ t - ℓ s ≤ D) (hk : D ≤ 2 ^ k) (h : Relation.ReflTransGen r s t) :
    SavitchMidpoint r k s t := by
  obtain ⟨n, hn⟩ := savitch_depth_topological_potential_bound_of_reflTransGen h
  have hpot := savitch_depth_topological_potential_bound_pot hℓ hn
  have hn_le : n ≤ 2 ^ k := by omega
  exact savitch_depth_topological_potential_bound_midpoint k hn_le hn
