import AFTD.Prelude
import AFTD.Kb.Tcs.Op193CubicThresholdEdgeGap
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_193_cubic_cycle_anchor_avoidance

Topic: graphs   Node: 0aaafc392bc3

Provenance: helper lemma. Clique-free extremal reduction for the anchored-color argument in arXiv:2610.17884 Section 3.

On any cycle of length at least k times ((k-1)^2+1), every family of m-2k+2 subsets of size at most k admits a stable k-set meeting each member in at most one vertex.
-/

namespace Inbox777CubicAvoid
variable (m q : ℕ) (A : Fin q → Finset (Fin m))
def graph : SimpleGraph (Fin m) where
  Adj x y := x ≠ y ∧ ¬(SimpleGraph.cycleGraph m).Adj x y ∧ ∀ j, ¬(x ∈ A j ∧ y ∈ A j)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_, ?_⟩
    · intro hxy; exact h.2.1 hxy.symm
    · intro j hxy; exact h.2.2 j ⟨hxy.2, hxy.1⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem clique_avoids (k : ℕ) (S : Finset (Fin m)) (hs : (graph m q A).IsNClique k S) :
    S.card = k ∧ (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m)) ∧
      ∀ j, (S ∩ A j).card ≤ 1 := by
  refine ⟨hs.card_eq, ?_, ?_⟩
  · intro x hx y hy hxy hxy'
    exact ((hs.isClique hx hy hxy).2.1) hxy'
  · intro j
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hxS := (Finset.mem_inter.mp hx).1
    have hyS := (Finset.mem_inter.mp hy).1
    have hxA := (Finset.mem_inter.mp hx).2
    have hyA := (Finset.mem_inter.mp hy).2
    exact ((hs.isClique hxS hyS hxy).2.2 j) ⟨hxA,hyA⟩
end Inbox777CubicAvoid

open scoped BigOperators
open Finset SimpleGraph
noncomputable instance (m q : ℕ) (A : Fin q → Finset (Fin m)) :
    DecidableRel (Inbox777CubicAvoid.graph m q A).Adj := Classical.decRel _

theorem in777_cubic_edge_count (m q k : ℕ) (hm : 3 ≤ m)
    (A : Fin q → Finset (Fin m)) (hA : ∀ j, (A j).card ≤ k) :
    m*(m-3) ≤ 2*(Inbox777CubicAvoid.graph m q A).edgeFinset.card + q*k*(k-1) := by
  classical
  let G := Inbox777CubicAvoid.graph m q A
  let C := SimpleGraph.cycleGraph m
  let all : Finset (Fin m × Fin m) := Finset.univ.offDiag
  let good : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  let cyc : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => C.Adj p.1 p.2)
  let barred : Finset (Fin m × Fin m) := Finset.univ.biUnion (fun j => (A j).offDiag)
  have hcover : all ⊆ good ∪ cyc ∪ barred := by
    intro p hp
    obtain ⟨hp1,hp2,hne⟩ := Finset.mem_offDiag.mp hp
    by_cases hc : C.Adj p.1 p.2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [cyc,hc]))
    · by_cases ha : ∃ j, p.1 ∈ A j ∧ p.2 ∈ A j
      · obtain ⟨j,hx,hy⟩ := ha
        apply Finset.mem_union_right
        simp only [barred, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨j, Finset.mem_offDiag.mpr ⟨hx,hy,hne⟩⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hne,hc,fun j hj => ha ⟨j,hj⟩⟩
  have hall : all.card = m*m-m := by simp [all, Finset.offDiag_card]
  have hgood : good.card = 2*G.edgeFinset.card := by
    symm
    exact G.two_mul_card_edgeFinset
  have hdeg : ∀ v : Fin m, C.degree v = 2 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm
    have hm' : m = n+3 := by omega
    clear hn
    subst m
    intro v
    simpa [C] using (SimpleGraph.cycleGraph_degree_three_le (v := v))
  have hcyc : cyc.card = 2*m := by
    have he := C.sum_degrees_eq_twice_card_edges
    have hh := C.two_mul_card_edgeFinset
    change 2*C.edgeFinset.card = cyc.card at hh
    calc
      cyc.card = 2*C.edgeFinset.card := hh.symm
      _ = ∑ v : Fin m, C.degree v := he.symm
      _ = 2*m := by simp [hdeg, Nat.mul_comm]
  have hbar : barred.card ≤ q*(k*(k-1)) := by
    have hb := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin q))
      (fun j => (A j).offDiag) (k*(k-1)) (by
        intro j _
        rw [Finset.offDiag_card]
        have hid : (A j).card*(A j).card-(A j).card = (A j).card*((A j).card-1) := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        rw [hid]
        exact Nat.mul_le_mul (hA j) (Nat.sub_le_sub_right (hA j) 1))
    simpa [barred] using hb
  have hcard : all.card ≤ good.card + cyc.card + barred.card := by
    calc
      all.card ≤ (good ∪ cyc ∪ barred).card := Finset.card_le_card hcover
      _ ≤ (good ∪ cyc).card + barred.card := Finset.card_union_le _ _
      _ ≤ good.card + cyc.card + barred.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  rw [hall,hgood,hcyc] at hcard
  have hm3 : m * (m-3) = m*m - 3*m := by rw [Nat.mul_sub_left_distrib]; omega
  rw [hm3]
  have hbar' : barred.card ≤ q*k*(k-1) := by simpa [Nat.mul_assoc] using hbar
  change m*m-m ≤ 2*(Inbox777CubicAvoid.graph m q A).edgeFinset.card + 2*m + barred.card at hcard
  omega

theorem in777_cubic_clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 0 < r)
    (hfree : G.CliqueFree (r+1)) :
    2*r*G.edgeFinset.card ≤ (r-1)*(Fintype.card V)^2 := by
  obtain ⟨H, hd, hmax⟩ := exists_isTuranMaximal (V := V) hr
  letI : DecidableRel H.Adj := hd
  have hle : G.edgeFinset.card ≤ H.edgeFinset.card := hmax.2 hfree
  have heq : H.edgeFinset.card = (turanGraph (Fintype.card V) r).edgeFinset.card :=
    ((isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp hmax).some.card_edgeFinset_eq
  calc
    2*r*G.edgeFinset.card ≤ 2*r*H.edgeFinset.card := Nat.mul_le_mul_left _ hle
    _ = 2*r*(turanGraph (Fintype.card V) r).edgeFinset.card := by rw [heq]
    _ ≤ (r-1)*(Fintype.card V)^2 := mul_card_edgeFinset_turanGraph_le

theorem op_193_cubic_cycle_anchor_avoidance (k m : ℕ) (hk : 3 ≤ k)
    (hm : k * ((k-1)^2 + 1) ≤ m)
    (A : Fin (m-2*k+2) → Finset (Fin m))
    (hA : ∀ j, (A j).card ≤ k) :
    ∃ S : Finset (Fin m), S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m)) ∧
      ∀ j, (S ∩ A j).card ≤ 1 := by
  classical
  let q := m-2*k+2
  let G := Inbox777CubicAvoid.graph m q A
  have hfactor : 2 ≤ (k-1)^2+1 := by
    have hh : 1 ≤ k-1 := by omega
    nlinarith
  have h2k : 2*k ≤ m := by
    have hh := Nat.mul_le_mul_left k hfactor
    nlinarith
  have hm3 : 3 ≤ m := by omega
  by_contra hn
  have hfree : G.CliqueFree k := by
    intro S hS
    exact hn ⟨S, Inbox777CubicAvoid.clique_avoids m q A k S hS⟩
  have hr : 0 < k-1 := by omega
  have hfree' : G.CliqueFree ((k-1)+1) := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hfree
  have hupper := in777_cubic_clique_bound G (k-1) hr hfree'
  simp only [Fintype.card_fin] at hupper
  have hlower := in777_cubic_edge_count m q k hm3 A hA
  have hmR : (k : ℝ) * ((((k-1 : ℕ) : ℝ))^2 + 1) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Nat.cast_sub (by omega : 1 ≤ k)] at hmR
  norm_num at hmR
  have hgap := op_193_cubic_threshold_edge_gap (k : ℝ) (m : ℝ) (by exact_mod_cast hk) hmR
  have hq : (q : ℝ) = (m : ℝ)-2*(k : ℝ)+2 := by
    dsimp [q]
    rw [Nat.cast_add, Nat.cast_sub h2k]
    push_cast
    ring
  have hlowerR : ((m*(m-3) : ℕ) : ℝ) ≤
      ((2*G.edgeFinset.card + q*k*(k-1) : ℕ) : ℝ) := by exact_mod_cast hlower
  have hupperR : ((2*(k-1)*G.edgeFinset.card : ℕ) : ℝ) ≤
      (((k-1-1)*m^2 : ℕ) : ℝ) := by exact_mod_cast hupper
  push_cast [Nat.cast_sub (by omega : 3 ≤ m), Nat.cast_sub (by omega : 1 ≤ k),
    Nat.cast_sub (by omega : 1 ≤ k-1)] at hlowerR hupperR
  rw [hq] at hlowerR
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hlowerR (show 0 ≤ (k : ℝ)-1 by linarith)
  nlinarith
