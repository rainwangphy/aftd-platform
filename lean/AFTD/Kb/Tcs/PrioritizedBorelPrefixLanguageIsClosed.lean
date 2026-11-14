import AFTD.Prelude

/-!
# prioritized_borel_prefix_language_isClosed

Topic: automata   Node: 2cbf6a174ca5

Provenance: helper lemma. IN-829: compactness route to finite compatible plays.

For any predicate on finite words over a discrete topological alphabet, the set of infinite sequences all of whose finite prefixes satisfy it is closed.
-/

theorem prioritized_borel_prefix_language_isClosed
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A]
    (P : List A → Prop) :
    IsClosed {f : ℕ → A | ∀ n : ℕ, P (List.ofFn (fun i : Fin n => f i))} := by
  have he : {f : ℕ → A | ∀ n : ℕ, P (List.ofFn (fun i : Fin n => f i))} =
      ⋂ n : ℕ, {f : ℕ → A | P (List.ofFn (fun i : Fin n => f i))} := by
    ext f
    simp
  rw [he]
  apply isClosed_iInter
  intro n
  let T : Set (Fin n → A) := {f | P (List.ofFn f)}
  have hT : IsClosed T := isClosed_discrete T
  have hc : Continuous (fun f : ℕ → A => fun i : Fin n => f i) := by
    refine continuous_pi (fun i : Fin n => ?_)
    exact continuous_apply (i : ℕ)
  exact hT.preimage hc
