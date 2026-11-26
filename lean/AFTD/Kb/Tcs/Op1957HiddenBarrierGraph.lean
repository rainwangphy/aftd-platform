import AFTD.Prelude

/-!
# op1957_hidden_barrier_graph

Topic: graphs   Node: ec52db3a05df

Provenance: helper lemma. OP-1957; hidden barrier relaxation, experiment 40492.

A balanced join of two 20-vertex hub-and-triangle graphs, with six cross edges deleted at one hub; auxiliary finite sets encode the matching witness.
-/

def op1957_hidden_barrier_graph : SimpleGraph (Fin 40) where
  Adj u v := u ≠ v ∧
    ( (u.val < 20 ∧ 20 ≤ v.val ∧ ¬ (v.val = 20 ∧ u.val ∈ [4,7,10,13,16,19])) ∨
      (v.val < 20 ∧ 20 ≤ u.val ∧ ¬ (u.val = 20 ∧ v.val ∈ [4,7,10,13,16,19])) ∨
      (((u.val < 20 ∧ v.val < 20) ∨ (20 ≤ u.val ∧ 20 ≤ v.val)) ∧
        (((u.val % 20 = 0 ∧ 1 ≤ v.val % 20 ∧ v.val % 20 ≤ 10) ∨
          (v.val % 20 = 0 ∧ 1 ≤ u.val % 20 ∧ u.val % 20 ≤ 10)) ∨
          (2 ≤ u.val % 20 ∧ 2 ≤ v.val % 20 ∧ (u.val % 20-2)/3 = (v.val % 20-2)/3))))
  symm := ⟨by
    intro u v h
    rcases h with ⟨hne,h⟩
    refine ⟨hne.symm,?_⟩
    simp only [eq_comm, and_comm, or_comm, or_left_comm, or_assoc] at *
    tauto⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel op1957_hidden_barrier_graph.Adj := by
  intro u v
  unfold op1957_hidden_barrier_graph
  dsimp
  infer_instance

def in1209_hidden_U : Finset (Fin 40) := {4,7,10,13,16,19}
def in1209_hidden_S : Finset (Fin 40) := {0,2,3,20,21,22,23,24,25,26,27,28,29,30,31,32,34,35,37,38}
def in1209_hidden_R : Finset (Fin 40) := Finset.univ \ in1209_hidden_S

def in1209_hidden_mate (v : Fin 40) : Fin 40 :=
  if v=0 then 24 else if v=24 then 0 else
  if v=2 then 27 else if v=27 then 2 else
  if v=3 then 30 else if v=30 then 3 else
  if v=20 then 21 else if v=21 then 20 else
  if v=22 then 23 else if v=23 then 22 else
  if v=25 then 26 else if v=26 then 25 else
  if v=28 then 29 else if v=29 then 28 else
  if v=31 then 32 else if v=32 then 31 else
  if v=34 then 35 else if v=35 then 34 else
  if v=37 then 38 else if v=38 then 37 else v

def in1209_hidden_group (i : Fin 7) : Finset (Fin 40) :=
  if i=0 then {1} else if i=1 then {4} else if i=2 then {5,6,7} else
  if i=3 then {8,9,10} else if i=4 then {11,12,13} else
  if i=5 then {14,15,16} else {17,18,19}
