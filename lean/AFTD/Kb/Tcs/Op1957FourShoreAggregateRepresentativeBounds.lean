import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FourShoreRepresentativeBudget
import AFTD.Kb.Tcs.Op1957FourBlockSdiffCardSum
import AFTD.Kb.Tcs.Op1957FourShoreOtherCountsSumIdentity

/-!
# op1957_four_shore_aggregate_representative_bounds

Topic: graphs   Node: e36ae7eb5e6f

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore aggregate representative bounds.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_aggregate_representative_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F B : Fin 4 → Finset V) (E : Finset V) (x y : V)
    (forbid : Fin 4 → Fin 4) (L : ℕ)
    (hFdis : ∀ i l : Fin 4, i ≠ l → Disjoint (F i) (F l))
    (hEdis : ∀ i : Fin 4, Disjoint (F i) E)
    (hBdis : ∀ i l : Fin 4, i ≠ l → Disjoint (B i) (B l))
    (hBcover : (Finset.univ : Finset (Fin 4)).biUnion B = Finset.univ)
    (hEB : E ⊆ B 1) (hx : x ∈ B 0) (hy : y ∈ B 2)
    (hcross : ∀ i l : Fin 4, i ≠ l → ∀ a ∈ F i, ∀ b ∈ F l, G.Adj a b →
      (i=0 ∧ l=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ l=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i : Fin 4, ∀ a ∈ F i, ∀ w ∈ E, ¬ G.Adj a w)
    (hbf : ∀ b, b ≠ forbid b)
    (hforbid : ∀ b, ∀ a ∈ B b, ∀ w ∈ B (forbid b), ¬ G.Adj a w)
    (hblocks : ∀ b, (B b).card+(B (forbid b)).card=L)
    (hmin : ∀ b, 3 ≤ (B b).card)
    (hV : Fintype.card V=2*L)
    (hdegree : ∀ v, L+2 ≤ (G.neighborFinset v).card) :
    let g : Fin 4 → Fin 4 → ℕ := fun i b => (F i ∩ B b).card
    let tot : Fin 4 → ℕ := fun b => (∑ i : Fin 4, g i b) + (if b=1 then E.card else 0)
    ∀ j b : Fin 4,
      (if (j=0 ∧ b=0) ∨ (j=1 ∧ b=2) then 2 else 1) ≤ g j b →
      (∑ t ∈ (Finset.univ : Finset (Fin 4)).erase (forbid b), (tot t-g j t))+3 ≤ (B b).card := by
  classical
  dsimp only
  intro j b hcount
  have hs : Fintype.card V = (B (forbid b)).card+(L+(B b).card-1)+1 := by
    have hh := hblocks b
    have hm := hmin b
    omega
  have hraw := op1957_four_shore_representative_budget G F B E x y
    hFdis hEdis hBdis hx hy hcross hEanti j b (forbid b) (hbf b) (hforbid b)
    L (hmin b) hs hdegree hcount
  have hdiff (i : Fin 4) : (F i \ B (forbid b)).card =
      ∑ t ∈ (Finset.univ : Finset (Fin 4)).erase (forbid b), (F i ∩ B t).card :=
    op1957_four_block_sdiff_card_sum B (F i) (forbid b) hBdis hBcover
  simp_rw [hdiff] at hraw
  have hediff : (E \ B (forbid b)).card = if forbid b=1 then 0 else E.card := by
    by_cases h : forbid b=1
    · have hsub : E ⊆ B (forbid b) := by simpa [h] using hEB
      have hh : E \ B (forbid b) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
      simp [h,hEB]
    · have hdis : Disjoint E (B (forbid b)) :=
        Finset.disjoint_of_subset_left hEB (hBdis 1 (forbid b) (Ne.symm h))
      simp [h,Finset.sdiff_eq_self_of_disjoint hdis]
  rw [hediff] at hraw
  have hsum := op1957_four_shore_other_counts_sum_identity
    (fun i t => (F i ∩ B t).card) E.card j (forbid b)
  rw [hsum]
  exact hraw
