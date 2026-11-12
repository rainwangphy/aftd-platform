import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# prioritized_borel_exponential_profile_frontier

Topic: automata   Node: 907e18ce5ae1

Provenance: helper lemma.

For every n, there is a set of 2^n pairs of length-n binary profiles in which distinct pairs are incomparable when both components are ordered lexicographically.
-/

theorem in784_complement_lex_reverses (n : ℕ) (p q : Fin n → Bool)
    (h : toLex p < toLex q) :
    toLex (fun i => !q i) < toLex (fun i => !p i) := by
  change Pi.Lex (· < ·) (· < ·) p q at h
  obtain ⟨i, hprev, hbit⟩ := h
  change Pi.Lex (· < ·) (· < ·) (fun i => !q i) (fun i => !p i)
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    change (!(q j)) = (!(p j))
    rw [hprev j hj]
  · cases hp : p i <;> cases hq : q i <;> simp_all

theorem in784_complement_profiles_pareto (n : ℕ) (p q : Fin n → Bool)
    (hfirst : toLex p ≤ toLex q)
    (hsecond : toLex (fun i => !p i) ≤ toLex (fun i => !q i)) : p = q := by
  by_contra hne
  have hnelex : toLex p ≠ toLex q := by
    intro h
    apply hne
    exact congrArg ofLex h
  have hlt : toLex p < toLex q := lt_of_le_of_ne hfirst hnelex
  have hreverse := in784_complement_lex_reverses n p q hlt
  exact (not_lt_of_ge hsecond) hreverse

theorem prioritized_borel_exponential_profile_frontier (n : ℕ) :
    ∃ S : Finset ((Fin n → Bool) × (Fin n → Bool)),
      S.card = 2^n ∧
      ∀ x ∈ S, ∀ y ∈ S,
        toLex x.1 ≤ toLex y.1 → toLex x.2 ≤ toLex y.2 → x = y := by
  classical
  let make : (Fin n → Bool) → (Fin n → Bool) × (Fin n → Bool) :=
    fun p => (p, fun i => !p i)
  have hinj : Function.Injective make := by
    intro p q h
    exact congrArg Prod.fst h
  let S := Finset.univ.image make
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro x hx y hy hfirst hsecond
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    have heq : p = q := in784_complement_profiles_pareto n p q hfirst hsecond
    subst q
    rfl
