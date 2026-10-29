import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeCoil
import AFTD.Kb.Tcs.SimpleGraphHypercube
import AFTD.Kb.Tcs.G

/-!
# exists_hypercube_coil

Topic: combinatorics   Node: 0386f2069ad1

Provenance: helper lemma. arXiv:2610.36461 Section 1

For every n ≥ 2, there exists a coil in the hypercube Q_n.
-/

instance exists_hypercube_coil_decidable_exists_unique {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    Decidable (∃! x, p x) := by
  dsimp [ExistsUnique]
  infer_instance

instance exists_hypercube_coil_decidable_simple_graph_hypercube_adj (n : ℕ) :
    DecidableRel (simple_graph_hypercube n).Adj := by
  intro x y
  dsimp [simple_graph_hypercube, SimpleGraph.fromRel]
  infer_instance

def exists_hypercube_coil_e_fin : Fin 4 → (Fin 2 → Bool)
  | 0 => fun _ => false
  | 1 => fun i => i = 0
  | 2 => fun _ => true
  | 3 => fun i => i = 1

lemma exists_hypercube_coil_adj_map :
    ∀ a b : Fin 4, (simple_graph_hypercube 2).Adj (exists_hypercube_coil_e_fin a) (exists_hypercube_coil_e_fin b) ↔ (SimpleGraph.cycleGraph 4).Adj a b := by
  decide

lemma exists_hypercube_coil_e_fin_bij : Function.Bijective exists_hypercube_coil_e_fin := by
  decide

noncomputable def exists_hypercube_coil_e_iso : simple_graph_hypercube 2 ≃g SimpleGraph.cycleGraph 4 :=
  (RelIso.mk (Equiv.ofBijective exists_hypercube_coil_e_fin exists_hypercube_coil_e_fin_bij)
    (fun {a b} => exists_hypercube_coil_adj_map a b)).symm

def exists_hypercube_coil_i0 (n : ℕ) (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩
def exists_hypercube_coil_i1 (n : ℕ) (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

lemma exists_hypercube_coil_i0_ne_i1 (n : ℕ) (hn : 2 ≤ n) :
    exists_hypercube_coil_i0 n hn ≠ exists_hypercube_coil_i1 n hn := by
  intro h
  have : (0 : ℕ) = 1 := Fin.mk.inj h
  exact Nat.zero_ne_one this

def exists_hypercube_coil_pad (n : ℕ) (hn : 2 ≤ n) (u : Fin 2 → Bool) : Fin n → Bool :=
  fun i =>
    if i = exists_hypercube_coil_i0 n hn then u 0
    else if i = exists_hypercube_coil_i1 n hn then u 1
    else false

lemma exists_hypercube_coil_pad_i0 (n : ℕ) (hn : 2 ≤ n) (u : Fin 2 → Bool) :
    exists_hypercube_coil_pad n hn u (exists_hypercube_coil_i0 n hn) = u 0 := by
  change (if (exists_hypercube_coil_i0 n hn = exists_hypercube_coil_i0 n hn) then u 0 else _) = u 0
  rw [if_pos rfl]

lemma exists_hypercube_coil_pad_i1 (n : ℕ) (hn : 2 ≤ n) (u : Fin 2 → Bool) :
    exists_hypercube_coil_pad n hn u (exists_hypercube_coil_i1 n hn) = u 1 := by
  change (if (exists_hypercube_coil_i1 n hn = exists_hypercube_coil_i0 n hn) then _
    else if (exists_hypercube_coil_i1 n hn = exists_hypercube_coil_i1 n hn) then u 1 else _) = u 1
  rw [if_neg (Ne.symm (exists_hypercube_coil_i0_ne_i1 n hn)), if_pos rfl]

lemma exists_hypercube_coil_pad_other (n : ℕ) (hn : 2 ≤ n) (u : Fin 2 → Bool) (i : Fin n)
    (h0 : i ≠ exists_hypercube_coil_i0 n hn) (h1 : i ≠ exists_hypercube_coil_i1 n hn) :
    exists_hypercube_coil_pad n hn u i = false := by
  dsimp [exists_hypercube_coil_pad]
  rw [if_neg h0, if_neg h1]

lemma exists_hypercube_coil_pad_diff (n : ℕ) (hn : 2 ≤ n) (u v : Fin 2 → Bool) (i : Fin n)
    (h : exists_hypercube_coil_pad n hn u i ≠ exists_hypercube_coil_pad n hn v i) :
    i = exists_hypercube_coil_i0 n hn ∨ i = exists_hypercube_coil_i1 n hn := by
  by_contra hc
  have h0 : i ≠ exists_hypercube_coil_i0 n hn := fun h' => hc (Or.inl h')
  have h1 : i ≠ exists_hypercube_coil_i1 n hn := fun h' => hc (Or.inr h')
  have hu := exists_hypercube_coil_pad_other n hn u i h0 h1
  have hv := exists_hypercube_coil_pad_other n hn v i h0 h1
  rw [hu, hv] at h
  exact h rfl

lemma exists_hypercube_coil_pad_inj (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (exists_hypercube_coil_pad n hn) := by
  intro u v h
  ext ⟨i, hi⟩
  interval_cases i
  · have := congr_fun h (exists_hypercube_coil_i0 n hn)
    rwa [exists_hypercube_coil_pad_i0, exists_hypercube_coil_pad_i0] at this
  · have := congr_fun h (exists_hypercube_coil_i1 n hn)
    rwa [exists_hypercube_coil_pad_i1, exists_hypercube_coil_pad_i1] at this

lemma exists_hypercube_coil_hypercube_adj_iff (n : ℕ) (x y : Fin n → Bool) :
    (simple_graph_hypercube n).Adj x y ↔ ∃! i : Fin n, x i ≠ y i := by
  dsimp [simple_graph_hypercube, SimpleGraph.fromRel]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rcases h with ⟨i, hi, huniq⟩
      refine ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rcases h with ⟨i, hi, -⟩
    exact hi rfl

lemma exists_hypercube_coil_pad_adj (n : ℕ) (hn : 2 ≤ n) (u v : Fin 2 → Bool) :
    (simple_graph_hypercube n).Adj (exists_hypercube_coil_pad n hn u) (exists_hypercube_coil_pad n hn v) ↔
    (simple_graph_hypercube 2).Adj u v := by
  rw [exists_hypercube_coil_hypercube_adj_iff, exists_hypercube_coil_hypercube_adj_iff]
  constructor
  · rintro ⟨i, hi, huniq⟩
    rcases exists_hypercube_coil_pad_diff n hn u v i hi with rfl | rfl
    · rw [exists_hypercube_coil_pad_i0, exists_hypercube_coil_pad_i0] at hi
      refine ⟨0, hi, ?_⟩
      intro j hj
      fin_cases j
      · rfl
      · exfalso
        have h1 : exists_hypercube_coil_pad n hn u (exists_hypercube_coil_i1 n hn) ≠
            exists_hypercube_coil_pad n hn v (exists_hypercube_coil_i1 n hn) := by
          rwa [exists_hypercube_coil_pad_i1, exists_hypercube_coil_pad_i1]
        have := huniq (exists_hypercube_coil_i1 n hn) h1
        exact exists_hypercube_coil_i0_ne_i1 n hn this.symm
    · rw [exists_hypercube_coil_pad_i1, exists_hypercube_coil_pad_i1] at hi
      refine ⟨1, hi, ?_⟩
      intro j hj
      fin_cases j
      · exfalso
        have h0 : exists_hypercube_coil_pad n hn u (exists_hypercube_coil_i0 n hn) ≠
            exists_hypercube_coil_pad n hn v (exists_hypercube_coil_i0 n hn) := by
          rwa [exists_hypercube_coil_pad_i0, exists_hypercube_coil_pad_i0]
        have := huniq (exists_hypercube_coil_i0 n hn) h0
        exact exists_hypercube_coil_i0_ne_i1 n hn this
      · rfl
  · rintro ⟨j, hj, huniq⟩
    fin_cases j
    · refine ⟨exists_hypercube_coil_i0 n hn, ?_, ?_⟩
      · dsimp
        rwa [exists_hypercube_coil_pad_i0, exists_hypercube_coil_pad_i0]
      · intro i hi
        rcases exists_hypercube_coil_pad_diff n hn u v i hi with rfl | rfl
        · rfl
        · exfalso
          rw [exists_hypercube_coil_pad_i1, exists_hypercube_coil_pad_i1] at hi
          have := huniq 1 hi
          contradiction
    · refine ⟨exists_hypercube_coil_i1 n hn, ?_, ?_⟩
      · dsimp
        rwa [exists_hypercube_coil_pad_i1, exists_hypercube_coil_pad_i1]
      · intro i hi
        rcases exists_hypercube_coil_pad_diff n hn u v i hi with rfl | rfl
        · exfalso
          rw [exists_hypercube_coil_pad_i0, exists_hypercube_coil_pad_i0] at hi
          have := huniq 0 hi
          contradiction
        · rfl

lemma exists_hypercube_coil_induce_congr {V : Type*} (G : SimpleGraph V) {s t : Set V} (h : s = t)
    {W : Type*} {H : SimpleGraph W} (iso : G.induce t ≃g H) : Nonempty (G.induce s ≃g H) := by
  cases h
  exact ⟨iso⟩

/-- Existence of a coil in Q_n for n ≥ 2. -/
theorem exists_hypercube_coil (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Finset (Fin n → Bool), hypercube_coil n S := by
  let pad := exists_hypercube_coil_pad n hn
  have hpad_inj := exists_hypercube_coil_pad_inj n hn
  have hpad_adj := exists_hypercube_coil_pad_adj n hn
  let S : Finset (Fin n → Bool) := Finset.univ.image pad
  use S
  dsimp [hypercube_coil]
  have hcard : S.card = 4 := by
    change (Finset.univ.image pad).card = 4
    rw [Finset.card_image_of_injective _ hpad_inj]
    rfl
  refine ⟨by omega, ?_⟩
  have hrange : (S : Set (Fin n → Bool)) = Set.range pad := by
    simp [S]
  rw [hcard]
  have iso1 : ((simple_graph_hypercube n).induce (Set.range pad)) ≃g simple_graph_hypercube 2 :=
    (RelIso.mk (Equiv.ofInjective pad hpad_inj) (fun {a b} => hpad_adj a b)).symm
  have iso2 : simple_graph_hypercube 2 ≃g SimpleGraph.cycleGraph 4 := exists_hypercube_coil_e_iso
  have iso : ((simple_graph_hypercube n).induce (Set.range pad)) ≃g SimpleGraph.cycleGraph 4 :=
    RelIso.trans iso1 iso2
  exact exists_hypercube_coil_induce_congr (simple_graph_hypercube n) hrange iso
