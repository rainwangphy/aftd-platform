import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.Tcs.F

/-!
# zero_forcing_pair_obstruction_transitive

Topic: graphs   Node: da439d611723

Provenance: helper lemma.

For three distinct vertices each of whose singleton white sets is fort-free, the relation that a two-vertex white set is not fort-free is transitive.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN800PairObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

def twin (G : SimpleGraph V) (a b : V) : Prop :=
  ∀ u : V, u ≠ a → u ≠ b → (G.Adj u a ↔ G.Adj u b)

lemma bad_pair_is_twin (G : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (ha : is_zero_forcing_set G ((Finset.univ \ ({a} : Finset V) : Finset V) : Set V))
    (hb : is_zero_forcing_set G ((Finset.univ \ ({b} : Finset V) : Finset V) : Set V))
    (hbad : ¬ is_zero_forcing_set G ((Finset.univ \ ({a,b} : Finset V) : Finset V) : Set V)) :
    twin G a b := by
  classical
  have hnot : ¬ ¬ ∃ F : Finset V, F.Nonempty ∧ F ⊆ ({a,b} : Finset V) ∧
      (∀ u : V, u ∉ F → ∀ w : V, w ∈ F → G.Adj u w →
        ∃ x : V, x ∈ F ∧ G.Adj u x ∧ x ≠ w) := by
    intro h
    exact hbad ((zfs_compl_iff_no_stuck G ({a,b} : Finset V)).mpr h)
  obtain ⟨F, hne, hsub, hfort⟩ := Classical.not_not.mp hnot
  have haF : a ∈ F := by
    by_contra haF
    have hFb : F ⊆ ({b} : Finset V) := by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa using hsub hx
      rcases hx' with rfl | rfl
      · exact (haF hx).elim
      · simp
    exact ((zfs_compl_iff_no_stuck G ({b} : Finset V)).mp hb) ⟨F, hne, hFb, hfort⟩
  have hbF : b ∈ F := by
    by_contra hbF
    have hFa : F ⊆ ({a} : Finset V) := by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa using hsub hx
      rcases hx' with rfl | rfl
      · simp
      · exact (hbF hx).elim
    exact ((zfs_compl_iff_no_stuck G ({a} : Finset V)).mp ha) ⟨F, hne, hFa, hfort⟩
  have hF : F = ({a,b} : Finset V) := by
    apply Finset.Subset.antisymm hsub
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haF, hbF⟩
  subst F
  intro u hua hub
  have hu : u ∉ ({a,b} : Finset V) := by simp [hua, hub]
  constructor
  · intro h
    obtain ⟨x, hx, hux, hxa⟩ := hfort u hu a (by simp) h
    have hx' : x = b := by simpa [hxa] using hx
    simpa [hx'] using hux
  · intro h
    obtain ⟨x, hx, hux, hxb⟩ := hfort u hu b (by simp) h
    have hx' : x = a := by simpa [hxb] using hx
    simpa [hx'] using hux

lemma twin_bad_pair (G : SimpleGraph V) (a b : V) (hab : a ≠ b) (h : twin G a b) :
    ¬ is_zero_forcing_set G ((Finset.univ \ ({a,b} : Finset V) : Finset V) : Set V) := by
  intro hforce
  apply ((zfs_compl_iff_no_stuck G ({a,b} : Finset V)).mp hforce)
  refine ⟨{a,b}, by simp, by intro x hx; exact hx, ?_⟩
  intro u hu w hw huw
  have hua : u ≠ a := by intro h'; apply hu; simp [h']
  have hub : u ≠ b := by intro h'; apply hu; simp [h']
  have hw' : w = a ∨ w = b := by simpa using hw
  rcases hw' with rfl | rfl
  · exact ⟨b, by simp, (h u hua hub).mp huw, Ne.symm hab⟩
  · exact ⟨a, by simp, (h u hua hub).mpr huw, hab⟩

lemma twin_trans (G : SimpleGraph V) (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (habT : twin G a b) (hbcT : twin G b c) : twin G a c := by
  intro u hua huc
  by_cases hub : u = b
  · subst u
    have h1 : G.Adj a b ↔ G.Adj a c := hbcT a hab hac
    have h2 : G.Adj c a ↔ G.Adj c b := habT c (Ne.symm hac) (Ne.symm hbc)
    constructor
    · intro hba
      have hab' : G.Adj a b := hba.symm
      have hac' : G.Adj a c := h1.mp hab'
      have hca : G.Adj c a := hac'.symm
      have hcb : G.Adj c b := h2.mp hca
      exact hcb.symm
    · intro hbc'
      have hcb : G.Adj c b := hbc'.symm
      have hca : G.Adj c a := h2.mpr hcb
      have hac' : G.Adj a c := hca.symm
      have hab' : G.Adj a b := h1.mpr hac'
      exact hab'.symm
  · exact (habT u hua hub).trans (hbcT u hub huc)

theorem transitive (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : is_zero_forcing_set G ((Finset.univ \ ({a} : Finset V) : Finset V) : Set V))
    (hb : is_zero_forcing_set G ((Finset.univ \ ({b} : Finset V) : Finset V) : Set V))
    (hc : is_zero_forcing_set G ((Finset.univ \ ({c} : Finset V) : Finset V) : Set V))
    (hab_bad : ¬ is_zero_forcing_set G ((Finset.univ \ ({a,b} : Finset V) : Finset V) : Set V))
    (hbc_bad : ¬ is_zero_forcing_set G ((Finset.univ \ ({b,c} : Finset V) : Finset V) : Set V)) :
    ¬ is_zero_forcing_set G ((Finset.univ \ ({a,c} : Finset V) : Finset V) : Set V) := by
  exact twin_bad_pair G a c hac (twin_trans G a b c hab hbc hac
    (bad_pair_is_twin G a b hab ha hb hab_bad)
    (bad_pair_is_twin G b c hbc hb hc hbc_bad))

end IN800PairObstruction

theorem zero_forcing_pair_obstruction_transitive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : is_zero_forcing_set G ((Finset.univ \ ({a} : Finset V) : Finset V) : Set V)) (hb : is_zero_forcing_set G ((Finset.univ \ ({b} : Finset V) : Finset V) : Set V)) (hc : is_zero_forcing_set G ((Finset.univ \ ({c} : Finset V) : Finset V) : Set V)) (hab_bad : ¬ is_zero_forcing_set G ((Finset.univ \ ({a,b} : Finset V) : Finset V) : Set V)) (hbc_bad : ¬ is_zero_forcing_set G ((Finset.univ \ ({b,c} : Finset V) : Finset V) : Set V)) : ¬ is_zero_forcing_set G ((Finset.univ \ ({a,c} : Finset V) : Finset V) : Set V) := by
  exact IN800PairObstruction.transitive G a b c hab hbc hac ha hb hc hab_bad hbc_bad
