import AFTD.Prelude

/-!
# condorcet_private_triple_stationarity_obstruction

Topic: social_choice   Node: 80ca47c001b8

Provenance: helper lemma. IN-357 method diagnostic for OP-19, experiments8922 and8923. This refutes a newly tested arbitrary-private-policy construction for the acyclic-weight-separation target. It is not a refutation of the election conjecture or of optimized policies, and is not a research advance. The finite relation is the residue tournament on19 vertices; all data and acyclicity are kernel checked.

There exist a strict tournament R on19 vertices with a common predecessor for every ordered triple, a chosen three-element set J(a) for every vertex a, natural vertex weights w, and an induced acyclic subset U. Each a is outside J(a), points to all of J(a), and is its unique common predecessor. The exact flow identity 3*w(b)=sum of w(a) over a with b in J(a) holds at every b. The total weight is35087, and U has weight22469, strictly above half. Thus some choice of private triples has stationary weights failing the required acyclic half bound. No claim is made about every policy or averaging over all private triples.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

def condorcet_private_stationary_relation (a b : Fin 19) : Prop :=
  (b-a).val ∈ ([1, 4, 5, 6, 7, 9, 11, 16, 17] : List ℕ)
instance : DecidableRel condorcet_private_stationary_relation := fun a b =>
  inferInstanceAs (Decidable ((b-a).val ∈ ([1, 4, 5, 6, 7, 9, 11, 16, 17] : List ℕ)))
def condorcet_private_stationary_triple : Fin 19 → Finset (Fin 19) := ![{6,11,17},{6,17,18},{6,8,11},{0,1,8},{1,2,9},{2,3,10},{3,11,15},{4,5,12},{6,15,17},{1,6,10},{0,2,8},{15,17,18},{0,2,9},{0,1,17},{6,11,15},{0,2,3},{1,2,14},{3,14,15},{3,6,15}]
def condorcet_private_stationary_weight : Fin 19 → ℕ := ![3610,1717,1893,5151,0,0,4206,0,2348,0,0,3656,0,0,1259,5679,0,3777,1791]
def condorcet_private_stationary_order : Fin 19 → ℕ := ![0,0,0,4,0,0,0,0,0,0,0,1,0,0,0,3,0,2,0]
def condorcet_private_stationary_set : Finset (Fin 19) := {6,11,17,15,3}

theorem condorcet_private_stationary_tournament :
    (∀ a, ¬condorcet_private_stationary_relation a a) ∧
    (∀ a b, a ≠ b →
      (condorcet_private_stationary_relation a b ↔
        ¬condorcet_private_stationary_relation b a)) := by decide

theorem condorcet_private_stationary_s3 : ∀ a b c : Fin 19,
    ∃ r, condorcet_private_stationary_relation r a ∧
      condorcet_private_stationary_relation r b ∧
      condorcet_private_stationary_relation r c := by decide

theorem condorcet_private_stationary_unique : ∀ a : Fin 19,
    (condorcet_private_stationary_triple a).card = 3 ∧
    a ∉ condorcet_private_stationary_triple a ∧
    (∀ b ∈ condorcet_private_stationary_triple a,
      condorcet_private_stationary_relation a b) ∧
    ∀ r, (∀ b ∈ condorcet_private_stationary_triple a,
      condorcet_private_stationary_relation r b) → r = a := by decide

theorem condorcet_private_stationary_flow : ∀ b : Fin 19,
    3 * condorcet_private_stationary_weight b =
      ∑ a : Fin 19, if b ∈ condorcet_private_stationary_triple a then
        condorcet_private_stationary_weight a else 0 := by decide

theorem condorcet_private_stationary_mass :
    (∑ a : Fin 19, condorcet_private_stationary_weight a) = 35087 ∧
    (∑ a ∈ condorcet_private_stationary_set, condorcet_private_stationary_weight a) = 22469 ∧
    0 < (∑ a : Fin 19, condorcet_private_stationary_weight a) ∧
    (∑ a : Fin 19, condorcet_private_stationary_weight a) <
      2 * (∑ a ∈ condorcet_private_stationary_set, condorcet_private_stationary_weight a) := by
  decide

theorem condorcet_private_stationary_ordered : ∀ a b : Fin 19,
    a ∈ condorcet_private_stationary_set → b ∈ condorcet_private_stationary_set →
    condorcet_private_stationary_relation a b →
    condorcet_private_stationary_order a < condorcet_private_stationary_order b := by decide

theorem condorcet_private_stationary_wellFounded :
    WellFounded (fun a b : {a : Fin 19 // a ∈ condorcet_private_stationary_set} =>
      condorcet_private_stationary_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 19 // a ∈ condorcet_private_stationary_set} =>
    condorcet_private_stationary_order a.val)).wf.mono ?_
  intro a b hab
  exact condorcet_private_stationary_ordered a.val b.val a.property b.property hab

theorem condorcet_private_triple_stationarity_obstruction :
    ∃ (R : Fin 19 → Fin 19 → Prop) (J : Fin 19 → Finset (Fin 19))
      (w : Fin 19 → ℕ) (U : Finset (Fin 19)),
      (∀ a, ¬ R a a) ∧
      (∀ a b, a ≠ b → (R a b ↔ ¬ R b a)) ∧
      (∀ a b c, ∃ r, R r a ∧ R r b ∧ R r c) ∧
      (∀ a, (J a).card = 3 ∧ a ∉ J a ∧
        (∀ b ∈ J a, R a b) ∧ ∀ r, (∀ b ∈ J a, R r b) → r = a) ∧
      (∀ b, 3 * w b = ∑ a, if b ∈ J a then w a else 0) ∧
      (∑ a, w a) = 35087 ∧ (∑ a ∈ U, w a) = 22469 ∧
      0 < (∑ a, w a) ∧ (∑ a, w a) < 2 * (∑ a ∈ U, w a) ∧
      WellFounded (fun a b : {a : Fin 19 // a ∈ U} => R a.val b.val) := by
  refine ⟨condorcet_private_stationary_relation, condorcet_private_stationary_triple,
    condorcet_private_stationary_weight, condorcet_private_stationary_set,
    condorcet_private_stationary_tournament.1, condorcet_private_stationary_tournament.2,
    condorcet_private_stationary_s3, condorcet_private_stationary_unique,
    condorcet_private_stationary_flow, ?_, ?_, ?_, ?_, condorcet_private_stationary_wellFounded⟩
  · exact condorcet_private_stationary_mass.1
  · exact condorcet_private_stationary_mass.2.1
  · exact condorcet_private_stationary_mass.2.2.1
  · exact condorcet_private_stationary_mass.2.2.2
