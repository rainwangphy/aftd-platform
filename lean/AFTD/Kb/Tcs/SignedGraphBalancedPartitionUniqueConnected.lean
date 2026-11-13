import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsBalancedPartition

/-!
# signed_graph_balanced_partition_unique_connected

Topic: combinatorics   Node: a799173b38be

Provenance: helper lemma. Balance-partition uniqueness needed to transfer the three-fixed-point subset theorem to signed graphs; see arXiv:2611.13901, Proposition 4.2.

Any two balance partitions of the same connected signed graph agree up to exchanging their two parts.
-/

namespace OP1525Unique

lemma bool_xor_square (a b c d : Bool) : xor a b = xor c d → xor a c = xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma bool_xor_solve (a b c : Bool) : xor a b = c → a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

lemma connected_labels {V : Type*} (G : SimpleGraph V) (hc : G.Connected) (a b : V → Bool)
    (he : ∀ u v, G.Adj u v → xor (a u) (a v) = xor (b u) (b v)) :
    ∃ c : Bool, ∀ x, a x = xor (b x) c := by
  letI : Nonempty V := hc.nonempty
  let r : V := Classical.choice inferInstance
  have hedge (u v : V) (h : G.Adj u v) : xor (a u) (b u) = xor (a v) (b v) :=
    bool_xor_square _ _ _ _ (he u v h)
  have hpath : ∀ x, Relation.ReflTransGen G.Adj r x → xor (a r) (b r) = xor (a x) (b x) := by
    intro x p
    induction p with
    | refl => rfl
    | tail _ h ih => exact ih.trans (hedge _ _ h)
  refine ⟨xor (a r) (b r), ?_⟩
  intro x
  exact bool_xor_solve _ _ _ (hpath x ((SimpleGraph.reachable_iff_reflTransGen r x).mp (hc r x))).symm

def color {V : Type*} [DecidableEq V] (A : Finset V) (v : V) : Bool := decide (v ∈ A)
def sign (p : Bool) : ℤ := if p then -1 else 1

lemma balanced_sign {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B)
    (u v : V) (h : G.graph.Adj u v) :
    G.sgn ⟨s(u, v), h⟩ = sign (xor (color A u) (color A v)) := by
  have hB (x : V) (hx : x ∉ A) : x ∈ B := by
    have hall : x ∈ A ∪ B := by rw [hbal.1]; exact Finset.mem_univ x
    exact (Finset.mem_union.mp hall).resolve_left hx
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).1 (Or.inl ⟨hu, hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).2 (Or.inl ⟨hu, hB v hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).2 (Or.inr ⟨hB u hu, hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).1 (Or.inr ⟨hB u hu, hB v hv⟩)

lemma sign_injective {a b : Bool} (h : sign a = sign b) : a = b := by
  cases a <;> cases b <;> simp [sign] at h ⊢

end OP1525Unique

open OP1525Unique

theorem signed_graph_balanced_partition_unique_connected {V : Type*} [DecidableEq V] [Fintype V]
    (G : SignedGraph V) (hconn : G.graph.Connected) (A B C D : Finset V)
    (hAB : G.IsBalancedPartition A B) (hCD : G.IsBalancedPartition C D) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  classical
  have hBA : B = Finset.univ \ A := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hxB hxA
      exact (Finset.disjoint_left.mp hAB.2.1) hxA hxB
    · intro hxA
      have hx : x ∈ A ∪ B := by rw [hAB.1]; exact Finset.mem_univ x
      exact (Finset.mem_union.mp hx).resolve_left hxA
  have hDC : D = Finset.univ \ C := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hxD hxC
      exact (Finset.disjoint_left.mp hCD.2.1) hxC hxD
    · intro hxC
      have hx : x ∈ C ∪ D := by rw [hCD.1]; exact Finset.mem_univ x
      exact (Finset.mem_union.mp hx).resolve_left hxC
  have he : ∀ u v, G.graph.Adj u v →
      xor (OP1525Unique.color A u) (OP1525Unique.color A v) =
        xor (OP1525Unique.color C u) (OP1525Unique.color C v) := by
    intro u v h
    apply sign_injective
    exact (balanced_sign G A B hAB u v h).symm.trans (balanced_sign G C D hCD u v h)
  obtain ⟨d, hd⟩ := connected_labels G.graph hconn (OP1525Unique.color A) (OP1525Unique.color C) he
  cases d with
  | false =>
    have hAC : A = C := by
      ext x
      have hx := hd x
      by_cases hxA : x ∈ A <;> by_cases hxC : x ∈ C <;>
        simp [OP1525Unique.color, hxA, hxC] at hx ⊢
    left
    exact ⟨hAC, by rw [hBA, hDC, hAC]⟩
  | true =>
    have hAD : A = D := by
      rw [hDC]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      have hx := hd x
      by_cases hxA : x ∈ A <;> by_cases hxC : x ∈ C <;>
        simp [OP1525Unique.color, hxA, hxC] at hx ⊢
    have hBC : B = C := by
      rw [hBA]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      have hx := hd x
      by_cases hxA : x ∈ A <;> by_cases hxC : x ∈ C <;>
        simp [OP1525Unique.color, hxA, hxC] at hx ⊢
    exact Or.inr ⟨hAD, hBC⟩
