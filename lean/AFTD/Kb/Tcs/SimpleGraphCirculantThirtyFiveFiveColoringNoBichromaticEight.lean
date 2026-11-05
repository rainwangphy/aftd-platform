import AFTD.Prelude

/-!
# simple_graph_circulant_thirty_five_five_coloring_no_bichromatic_eight

Topic: combinatorics   Node: de6827d312b9

Provenance: original. Related work: OP-926, experiment 14264: refutes the proposed universal bichromatic independent-eight-set shortcut.

The 35-vertex circulant graph with steps ±1, ±7, ±11, ±16 has a proper five-coloring in which every independent set of eight vertices uses at least three colors.
-/

namespace In555ColorBase

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def edge (u v : Fin 35) : Prop :=
  (u.val + 35 - v.val) % 35 ∈ ({1, 7, 11, 16, 19, 24, 28, 34} : Finset ℕ)

instance : DecidableRel edge := fun u v => by
  unfold edge
  infer_instance

def base : SimpleGraph (Fin 35) where
  Adj := edge
  symm := by
    constructor
    exact (show ∀ u v : Fin 35, edge u v → edge v u from by decide)
  loopless := by
    constructor
    exact (show ∀ u : Fin 35, ¬edge u u from by decide)

instance : DecidableRel base.Adj := fun u v => inferInstanceAs (Decidable (edge u v))

theorem identified (H : SimpleGraph (Fin 35))
    (h : ∀ u v, H.Adj u v ↔
      (u.val + 35 - v.val) % 35 ∈ ({1, 7, 11, 16, 19, 24, 28, 34} : Finset ℕ)) :
    H = base := by
  ext u v
  exact h u v

end In555ColorBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace In555ColorFast
open In555ColorBase

def color (v : Fin 35) : Fin 5 := ⟨v.val % 5, Nat.mod_lt _ (by decide)⟩
def pair (i j : Fin 5) : Finset (Fin 35) := Finset.univ.filter fun v => color v = i ∨ color v = j
def target (i : Fin 5) : Finset (Fin 35) := Finset.univ.filter fun v => color v = i
def shift (i j : Fin 5) : Nat :=
  if (j.val + 5 - i.val) % 5 = 1 then 34
  else if (j.val + 5 - i.val) % 5 = 2 then 28
  else if (j.val + 5 - i.val) % 5 = 3 then 7 else 1
def key (i j : Fin 5) (v : Fin 35) : Fin 35 :=
  if color v = i then v else ⟨(v.val + shift i j) % 35, Nat.mod_lt _ (by decide)⟩

theorem proper : ∀ u v, base.Adj u v → color u ≠ color v := by decide

theorem target_card (i : Fin 5) : (target i).card = 7 := by
  fin_cases i <;> decide

theorem key_maps (i j : Fin 5) : ∀ u ∈ pair i j, key i j u ∈ target i := by
  fin_cases i <;> fin_cases j <;> decide

theorem key_collision (i j : Fin 5) : ∀ u ∈ pair i j, ∀ v ∈ pair i j,
    key i j u = key i j v → u = v ∨ base.Adj u v := by
  fin_cases i <;> fin_cases j <;> decide

theorem no_bichromatic_eight (i j : Fin 5) (S : Finset (Fin 35))
    (hsub : S ⊆ pair i j) (hind : base.IsIndepSet S) : S.card ≤ 7 := by
  have hle : S.card ≤ (target i).card := by
    apply Finset.card_le_card_of_injOn (key i j)
    · intro u hu
      exact key_maps i j u (hsub hu)
    · intro u hu v hv heq
      rcases key_collision i j u (hsub hu) v (hsub hv) heq with h | h
      · exact h
      · exact False.elim (hind hu hv (base.ne_of_adj h) h)
  simpa [target_card] using hle
end In555ColorFast

theorem simple_graph_circulant_thirty_five_five_coloring_no_bichromatic_eight
    (H : SimpleGraph (Fin 35)) [DecidableRel H.Adj]
    (hcirc : ∀ u v, H.Adj u v ↔
      (u.val + 35 - v.val) % 35 ∈ ({1, 7, 11, 16, 19, 24, 28, 34} : Finset ℕ)) :
    ∃ c : Fin 35 → Fin 5,
      (∀ u v, H.Adj u v → c u ≠ c v) ∧
      (∀ S : Finset (Fin 35), S.card = 8 → H.IsIndepSet S →
        ∀ i j : Fin 5, ¬ (∀ v ∈ S, c v = i ∨ c v = j)) := by
  have hH : H = In555ColorBase.base := In555ColorBase.identified H hcirc
  subst H
  refine ⟨In555ColorFast.color, In555ColorFast.proper, ?_⟩
  intro S hcard hind i j hcolors
  have hsub : S ⊆ In555ColorFast.pair i j := by
    intro v hv
    simpa [In555ColorFast.pair] using hcolors v hv
  have hle := In555ColorFast.no_bichromatic_eight i j S hsub hind
  omega
