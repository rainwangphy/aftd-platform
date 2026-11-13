import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingFinsetStep
import AFTD.Kb.Tcs.ZeroForcingFinsetIter
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# zero_forcing_finset_iter_of_stable

Topic: graphs   Node: c58f4ee283f6

Provenance: helper lemma.

If a finite parallel forcing iteration has stabilized, the original blue set is zero forcing exactly when the stabilized set is all vertices.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IN800FiniteClosure

def step {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun w => ∃ u ∈ S, G.Adj u w ∧ ∀ x, G.Adj u x → x ≠ w → x ∈ S)

def iter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ) : Finset V :=
  (step G)^[k] S

lemma step_extends {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : S ⊆ step G S := Finset.subset_union_left

lemma step_sound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S B : Finset V)
    (hB : ∀ x ∈ B, ZeroForced G (S : Set V) x) :
    ∀ x ∈ step G B, ZeroForced G (S : Set V) x := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hB x hx
  · obtain ⟨u, hu, hux, hother⟩ := (Finset.mem_filter.mp hx).2
    exact ZeroForced.step u x (hB u hu) hux (fun y huy hyx => hB y (hother y huy hyx))

lemma iter_extends {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ) : S ⊆ iter G S k := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter, Function.iterate_succ_apply']
    exact ih.trans (step_extends G _)

lemma iter_sound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ) :
    ∀ x ∈ iter G S k, ZeroForced G (S : Set V) x := by
  induction k with
  | zero =>
    intro x hx
    exact ZeroForced.init x (by simpa [iter] using hx)
  | succ k ih =>
    rw [iter, Function.iterate_succ_apply']
    exact step_sound G S _ ih

lemma fixed_contains_forced {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S B : Finset V) (hSB : S ⊆ B) (hfix : step G B = B) :
    ∀ x, ZeroForced G (S : Set V) x → x ∈ B := by
  intro x hx
  induction hx with
  | init x hx => exact hSB hx
  | step u w hu huw hother ihu ihother =>
    have hw : w ∈ step G B := by
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, u, ihu, huw, fun x hux hxw => ihother x hux hxw⟩
    rwa [hfix] at hw

theorem certified_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ)
    (hstable : step G (iter G S k) = iter G S k) :
    is_zero_forcing_set G (S : Set V) ↔ iter G S k = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    exact fixed_contains_forced G S _ (iter_extends G S k) hstable x (h x)
  · intro h x
    apply iter_sound G S k x
    rw [h]
    exact Finset.mem_univ x

end IN800FiniteClosure

theorem zero_forcing_finset_iter_of_stable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (k : ℕ) (hstable : zero_forcing_finset_step G (zero_forcing_finset_iter G S k) = zero_forcing_finset_iter G S k) : is_zero_forcing_set G (S : Set V) ↔ zero_forcing_finset_iter G S k = Finset.univ := by
  exact IN800FiniteClosure.certified_iff G S k hstable
