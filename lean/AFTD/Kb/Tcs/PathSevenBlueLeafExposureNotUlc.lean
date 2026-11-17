import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Tcs.ZeroForcingFinsetIterDecides
import AFTD.Kb.Tcs.ZeroForcingFinsetIter
import AFTD.Kb.Tcs.IsZeroForcingSetMono

/-!
# path_seven_blue_leaf_exposure_not_ulc

Topic: graphs   Node: 94e852d1fd56

Provenance: helper lemma.

On a seven-vertex path with one endpoint fixed blue and the adjacent vertex as root, the exposure mixture at weight three quarters has normalized ranks 4, 5, 6 violating ultra-log-concavity.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN919Path

def G := SimpleGraph.pathGraph 7

instance : DecidableRel G.Adj := fun u v =>
  decidable_of_iff ((u : ℕ) + 1 = v ∨ (v : ℕ) + 1 = u) (SimpleGraph.pathGraph_adj.symm)

def expose (S : Finset (Fin 7)) : Prop := zero_forcing_root_exposed_fort G 1 S
instance (S : Finset (Fin 7)) : Decidable (expose S) := by
  unfold expose zero_forcing_root_exposed_fort
  infer_instance

def pattern (S : Finset (Fin 7)) : Prop :=
  (2 : Fin 7) ∈ S ∧ (6 : Fin 7) ∈ S ∧
  ((3 : Fin 7) ∈ S ∨ (4 : Fin 7) ∈ S) ∧
  ((4 : Fin 7) ∈ S ∨ (5 : Fin 7) ∈ S)
instance (S : Finset (Fin 7)) : Decidable (pattern S) := by unfold pattern; infer_instance

theorem endpoint_forces : is_zero_forcing_set G (({0} : Finset (Fin 7)) : Set (Fin 7)) := by
  apply (zero_forcing_finset_iter_decides G {0}).mpr
  decide

theorem allowed_forces (S : Finset (Fin 7)) (h : (0 : Fin 7) ∉ S) :
    is_zero_forcing_set G ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) := by
  apply is_zero_forcing_set_mono G _ endpoint_forces
  intro x hx
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
  subst x
  simpa using h

theorem expose_class : ∀ S : Finset (Fin 7), (0 : Fin 7) ∉ S → (expose S ↔ pattern S) := by
  decide

def a (k : ℕ) : Finset (Finset (Fin 7)) :=
  Finset.univ.filter fun S => (0 : Fin 7) ∉ S ∧ S.card = k ∧ ¬ pattern S

def c (k : ℕ) : Finset (Finset (Fin 7)) :=
  Finset.univ.filter fun S => (0 : Fin 7) ∉ S ∧ S.card = k ∧ pattern S

theorem count_a4 : (a 4).card = 11 := by decide
theorem count_c4 : (c 4).card = 4 := by decide
theorem count_a5 : (a 5).card = 2 := by decide
theorem count_c5 : (c 5).card = 4 := by decide
theorem count_a6 : (a 6).card = 0 := by decide
theorem count_c6 : (c 6).card = 1 := by decide



theorem count_a (k : ℕ) :
    {S : Finset (Fin 7) | (0 : Fin 7) ∉ S ∧ S.card = k ∧
      is_zero_forcing_set G ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧
      ¬ zero_forcing_root_exposed_fort G 1 S}.ncard = (a k).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext S
  simp only [Set.mem_toFinset, Set.mem_setOf_eq, a, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases h : (0 : Fin 7) ∈ S
  · simp [h]
  · have hf : is_zero_forcing_set G (Set.univ \ (S : Set (Fin 7))) := by simpa using allowed_forces S h
    have he := expose_class S h
    change zero_forcing_root_exposed_fort G 1 S ↔ pattern S at he
    simp [h, hf, he]

theorem count_c (k : ℕ) :
    {S : Finset (Fin 7) | (0 : Fin 7) ∉ S ∧ S.card = k ∧
      is_zero_forcing_set G ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧
      zero_forcing_root_exposed_fort G 1 S}.ncard = (c k).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext S
  simp only [Set.mem_toFinset, Set.mem_setOf_eq, c, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases h : (0 : Fin 7) ∈ S
  · simp [h]
  · have hf : is_zero_forcing_set G (Set.univ \ (S : Set (Fin 7))) := by simpa using allowed_forces S h
    have he := expose_class S h
    change zero_forcing_root_exposed_fort G 1 S ↔ pattern S at he
    simp [h, hf, he]


end IN919Path

theorem path_seven_blue_leaf_exposure_not_ulc : (let T := SimpleGraph.pathGraph 7; let p : Fin 7 := 1; let b : Fin 7 := 0; let a := fun k : ℕ => {S : Finset (Fin 7) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧ ¬ zero_forcing_root_exposed_fort T p S}.ncard; let c := fun k : ℕ => {S : Finset (Fin 7) | b ∉ S ∧ S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧ zero_forcing_root_exposed_fort T p S}.ncard; 4 * a 4 + 3 * c 4 = 56 ∧ 4 * a 5 + 3 * c 5 = 20 ∧ 4 * a 6 + 3 * c 6 = 3) := by
  let aa := fun k : ℕ => {S : Finset (Fin 7) | (0 : Fin 7) ∉ S ∧ S.card = k ∧
    is_zero_forcing_set IN919Path.G ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧
    ¬ zero_forcing_root_exposed_fort IN919Path.G 1 S}.ncard
  let cc := fun k : ℕ => {S : Finset (Fin 7) | (0 : Fin 7) ∉ S ∧ S.card = k ∧
    is_zero_forcing_set IN919Path.G ((Finset.univ \ S : Finset (Fin 7)) : Set (Fin 7)) ∧
    zero_forcing_root_exposed_fort IN919Path.G 1 S}.ncard
  change 4 * aa 4 + 3 * cc 4 = 56 ∧ 4 * aa 5 + 3 * cc 5 = 20 ∧ 4 * aa 6 + 3 * cc 6 = 3
  have ha4 : aa 4 = 11 := (IN919Path.count_a 4).trans IN919Path.count_a4
  have hc4 : cc 4 = 4 := (IN919Path.count_c 4).trans IN919Path.count_c4
  have ha5 : aa 5 = 2 := (IN919Path.count_a 5).trans IN919Path.count_a5
  have hc5 : cc 5 = 4 := (IN919Path.count_c 5).trans IN919Path.count_c5
  have ha6 : aa 6 = 0 := (IN919Path.count_a 6).trans IN919Path.count_a6
  have hc6 : cc 6 = 1 := (IN919Path.count_c 6).trans IN919Path.count_c6
  omega
