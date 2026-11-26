import AFTD.Prelude
import AFTD.Kb.Tcs.Multigraph
import AFTD.Kb.Tcs.MultigraphChromaticIndex
import AFTD.Kb.Tcs.MultigraphLocalChromaticIndex
import AFTD.Kb.Tcs.MultigraphIsLocallyBounded
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.MultigraphIsProperEdgeColoring
import AFTD.Kb.Tcs.MultigraphLocalBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# multigraph_local_to_ordinary_chromatic_index_gap_ge_two_exists

Topic: graphs   Node: 08187f0a716a

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:77

There exists a multigraph G on Fin n such that its local chromatic index exceeds its ordinary chromatic index by at least two: chi'_loc(G) - chi'(G) >= 2.
-/

/-- vertex of gadget `i` with role `r` (0,1,2 triangle; 3,4 the low pair) -/
def in1193_v (i r : Fin 5) : Fin 26 := ⟨5 * i.val + r.val, by omega⟩

/-- the hub -/
def in1193_hub : Fin 26 := ⟨25, by omega⟩

/-- edge multiplicities in units -/
def in1193_unit (u v : Fin 26) : ℕ :=
  if u.val = 25 then (if v.val ≠ 25 ∧ v.val % 5 = 2 then 1 else 0)
  else if v.val = 25 then (if u.val % 5 = 2 then 1 else 0)
  else if u.val / 5 = v.val / 5 then
    (([[0,1,2,1,1],[1,0,2,1,1],[2,2,0,0,0],[1,1,0,0,1],[1,1,0,1,0]] : List (List ℕ)).getD (u.val % 5) []).getD (v.val % 5) 0
  else 0

theorem in1193_unit_symm : ∀ u v, in1193_unit u v = in1193_unit v u := by decide +kernel

theorem in1193_unit_loop : ∀ u, in1193_unit u u = 0 := by decide +kernel

/-- five fat-triangle gadgets on a hub, all multiplicities scaled by 21 -/
def in1193_G : Multigraph (Fin 26) where
  mult := fun u v => 21 * in1193_unit u v
  symm := fun u v => by rw [in1193_unit_symm u v]
  loopless := fun u => by rw [in1193_unit_loop u]

/-- block table of the optimal colouring inside gadget `i` -/
def in1193_tA (i r s : ℕ) : Finset ℕ :=
  match r, s with
  | 0, 1 => {i} | 1, 0 => {i}
  | 1, 2 => {(i+1) % 5, (i+2) % 5} | 2, 1 => {(i+1) % 5, (i+2) % 5}
  | 0, 2 => {(i+3) % 5, (i+4) % 5} | 2, 0 => {(i+3) % 5, (i+4) % 5}
  | 0, 3 => {(i+1) % 5} | 3, 0 => {(i+1) % 5}
  | 0, 4 => {(i+2) % 5} | 4, 0 => {(i+2) % 5}
  | 1, 3 => {(i+3) % 5} | 3, 1 => {(i+3) % 5}
  | 1, 4 => {(i+4) % 5} | 4, 1 => {(i+4) % 5}
  | 3, 4 => {i} | 4, 3 => {i}
  | _, _ => ∅

/-- block table of the locally bounded colouring inside gadget `i` -/
def in1193_tB (i r s : ℕ) : Finset ℕ :=
  if i = 4 then
    match r, s with
    | 0, 1 => {4} | 1, 0 => {4}
    | 1, 2 => {1, 2} | 2, 1 => {1, 2}
    | 0, 2 => {3, 5} | 2, 0 => {3, 5}
    | 0, 3 => {1} | 3, 0 => {1}
    | 0, 4 => {2} | 4, 0 => {2}
    | 1, 3 => {3} | 3, 1 => {3}
    | 1, 4 => {5} | 4, 1 => {5}
    | 3, 4 => {0} | 4, 3 => {0}
    | _, _ => ∅
  else in1193_tA i r s

/-- block sets of a colouring given by a gadget table -/
def in1193_blk (t : ℕ → ℕ → ℕ → Finset ℕ) (u v : Fin 26) : Finset ℕ :=
  if u.val = 25 then (if v.val ≠ 25 ∧ v.val % 5 = 2 then {v.val / 5} else ∅)
  else if v.val = 25 then (if u.val % 5 = 2 then {u.val / 5} else ∅)
  else if u.val / 5 = v.val / 5 then t (u.val / 5) (u.val % 5) (v.val % 5)
  else ∅

/-- colours of a set of blocks; block `b` is `21 b + 1 .. 21 b + 21` -/
def in1193_col (S : Finset ℕ) : Finset ℕ := S.biUnion (fun b => Finset.Icc (21 * b + 1) (21 * b + 21))

theorem in1193_col_card (S : Finset ℕ) : (in1193_col S).card = 21 * S.card := by
  unfold in1193_col
  rw [Finset.card_biUnion]
  · simp [mul_comm]
  · intro a _ b _ hab
    show Disjoint (Finset.Icc (21 * a + 1) (21 * a + 21)) (Finset.Icc (21 * b + 1) (21 * b + 21))
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega

theorem in1193_col_disj (S T : Finset ℕ) (h : Disjoint S T) : Disjoint (in1193_col S) (in1193_col T) := by
  unfold in1193_col
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_biUnion, Finset.mem_Icc] at hx hy
  obtain ⟨b, hb, h1⟩ := hx
  obtain ⟨b', hb', h2⟩ := hy
  have : b = b' := by omega
  subst this
  exact Finset.disjoint_left.mp h hb hb'

theorem in1193_col_mem (S : Finset ℕ) (x : ℕ) (hx : x ∈ in1193_col S) : 1 ≤ x ∧ ∃ b ∈ S, x ≤ 21 * (b + 1) := by
  unfold in1193_col at hx
  simp only [Finset.mem_biUnion, Finset.mem_Icc] at hx
  obtain ⟨b, hb, h1⟩ := hx
  exact ⟨by omega, b, hb, by omega⟩

theorem in1193_proper_of_blocks (B : Fin 26 → Fin 26 → Finset ℕ) (m : ℕ)
    (h1 : ∀ u v, B u v = B v u) (h2 : ∀ u v, (B u v).card = in1193_unit u v)
    (h3 : ∀ u v, ∀ b ∈ B u v, b < m)
    (h4 : ∀ u v₁ v₂, v₁ ≠ v₂ → Disjoint (B u v₁) (B u v₂)) :
    multigraph_is_proper_edge_coloring in1193_G (21 * m) (fun u v => in1193_col (B u v)) := by
  refine ⟨fun u v => ?_, fun u v => ?_, fun u v x hx => ?_, fun u v₁ v₂ hv => in1193_col_disj _ _ (h4 u v₁ v₂ hv)⟩
  · show in1193_col (B u v) = in1193_col (B v u)
    rw [h1 u v]
  · show (in1193_col (B u v)).card = 21 * in1193_unit u v
    rw [in1193_col_card, h2 u v]
  · have hx : x ∈ in1193_col (B u v) := hx
    obtain ⟨hx1, b, hb, hx2⟩ := in1193_col_mem _ x hx
    have := h3 u v b hb
    exact ⟨hx1, by nlinarith⟩

theorem in1193_blocksA : (∀ u v, in1193_blk in1193_tA u v = in1193_blk in1193_tA v u) ∧
    (∀ u v, (in1193_blk in1193_tA u v).card = in1193_unit u v) ∧
    (∀ u v, ∀ b ∈ in1193_blk in1193_tA u v, b < 5) ∧
    (∀ u v₁ v₂, v₁ ≠ v₂ → Disjoint (in1193_blk in1193_tA u v₁) (in1193_blk in1193_tA u v₂)) := by
  decide +kernel

theorem in1193_blocksB : (∀ u v, in1193_blk in1193_tB u v = in1193_blk in1193_tB v u) ∧
    (∀ u v, (in1193_blk in1193_tB u v).card = in1193_unit u v) ∧
    (∀ u v, ∀ b ∈ in1193_blk in1193_tB u v, b < 6) ∧
    (∀ u v₁ v₂, v₁ ≠ v₂ → Disjoint (in1193_blk in1193_tB u v₁) (in1193_blk in1193_tB u v₂)) := by
  decide +kernel

theorem in1193_boundB : ∀ u v, ∀ b ∈ in1193_blk in1193_tB u v, 21 * (b + 1) ≤ multigraph_local_bound in1193_G u v := by
  decide +kernel

theorem in1193_facts : ∀ i : Fin 5,
    in1193_unit (in1193_v i 0) (in1193_v i 1) = 1 ∧ in1193_unit (in1193_v i 1) (in1193_v i 2) = 2 ∧
    in1193_unit (in1193_v i 0) (in1193_v i 2) = 2 ∧ in1193_unit (in1193_v i 0) (in1193_v i 3) = 1 ∧
    in1193_unit (in1193_v i 0) (in1193_v i 4) = 1 ∧ in1193_unit (in1193_v i 1) (in1193_v i 3) = 1 ∧
    in1193_unit (in1193_v i 1) (in1193_v i 4) = 1 ∧ in1193_unit (in1193_v i 3) (in1193_v i 4) = 1 ∧
    in1193_unit in1193_hub (in1193_v i 2) = 1 ∧
    multigraph_local_bound in1193_G (in1193_v i 3) (in1193_v i 4) = 84 := by
  decide +kernel

theorem in1193_v_inj : ∀ i j r s : Fin 5, in1193_v i r = in1193_v j s → i = j ∧ r = s := by decide +kernel

theorem in1193_v_ne_hub : ∀ i r : Fin 5, in1193_v i r ≠ in1193_hub := by decide +kernel

/-- indicator of a colour set -/
def in1193_ind (S : Finset ℕ) (z : ℕ) : ℕ := if z ∈ S then 1 else 0

theorem in1193_ind_le (S : Finset ℕ) (z : ℕ) : in1193_ind S z ≤ 1 := by
  unfold in1193_ind; split_ifs <;> omega

theorem in1193_ind_01 (S : Finset ℕ) (z : ℕ) : in1193_ind S z = 0 ∨ in1193_ind S z = 1 := by
  unfold in1193_ind; split_ifs <;> simp

theorem in1193_ind_disj {S T : Finset ℕ} (h : Disjoint S T) (z : ℕ) : in1193_ind S z + in1193_ind T z ≤ 1 := by
  unfold in1193_ind
  by_cases h1 : z ∈ S
  · have h2 : z ∉ T := Finset.disjoint_left.mp h h1
    simp [h1, h2]
  · simp only [h1, if_false]; split_ifs <;> omega

theorem in1193_ind_inter (S T : Finset ℕ) (z : ℕ) : in1193_ind S z + in1193_ind T z ≤ 1 + in1193_ind (S ∩ T) z := by
  unfold in1193_ind
  by_cases h1 : z ∈ S <;> by_cases h2 : z ∈ T <;> simp [h1, h2]

theorem in1193_ind_sum (S P : Finset ℕ) (h : S ⊆ P) : ∑ z ∈ P, in1193_ind S z = S.card := by
  unfold in1193_ind
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr h]; simp

theorem in1193_gadget (k N : ℕ) (hN : N = 5 * k + 1) (Mab Mbc Mac Ax Ay Bx By F W : Finset ℕ)
    (s1 : Mab ⊆ Finset.Icc 1 N) (s2 : Mbc ⊆ Finset.Icc 1 N) (s3 : Mac ⊆ Finset.Icc 1 N)
    (s4 : Ax ⊆ Finset.Icc 1 N) (s5 : Ay ⊆ Finset.Icc 1 N) (s6 : Bx ⊆ Finset.Icc 1 N)
    (s7 : By ⊆ Finset.Icc 1 N) (s8 : F ⊆ Finset.Icc 1 N) (s9 : W ⊆ Finset.Icc 1 N)
    (c1 : Mab.card = k) (c2 : Mbc.card = 2 * k) (c3 : Mac.card = 2 * k) (c4 : Ax.card = k)
    (c5 : Ay.card = k) (c6 : Bx.card = k) (c7 : By.card = k) (c8 : F.card = k) (c9 : W.card = k)
    (d1 : Disjoint Mab Mbc) (d2 : Disjoint Mab Mac) (d3 : Disjoint Mbc Mac)
    (d4 : Disjoint Mab Ax) (d5 : Disjoint Mab Ay) (d6 : Disjoint Mac Ax) (d7 : Disjoint Mac Ay)
    (d8 : Disjoint Ax Ay) (d9 : Disjoint Mab Bx) (d10 : Disjoint Mab By) (d11 : Disjoint Mbc Bx)
    (d12 : Disjoint Mbc By) (d13 : Disjoint Bx By) (d14 : Disjoint Mbc W) (d15 : Disjoint Mac W)
    (d16 : Disjoint Ax Bx) (d17 : Disjoint Ax F) (d18 : Disjoint Bx F) (d19 : Disjoint Ay By)
    (d20 : Disjoint Ay F) (d21 : Disjoint By F) : k ≤ (F ∩ W).card + 4 := by
  have key : ∀ z ∈ Finset.Icc 1 N, in1193_ind F z + in1193_ind W z
      + 3 * (in1193_ind Mab z + in1193_ind Mbc z + in1193_ind Mac z)
      + (in1193_ind Ax z + in1193_ind Ay z) + (in1193_ind Bx z + in1193_ind By z)
      ≤ 4 + in1193_ind (F ∩ W) z := by
    intro z _
    have e1 := in1193_ind_disj d1 z
    have e2 := in1193_ind_disj d2 z
    have e3 := in1193_ind_disj d3 z
    have e4 := in1193_ind_disj d4 z
    have e5 := in1193_ind_disj d5 z
    have e6 := in1193_ind_disj d6 z
    have e7 := in1193_ind_disj d7 z
    have e8 := in1193_ind_disj d8 z
    have e9 := in1193_ind_disj d9 z
    have e10 := in1193_ind_disj d10 z
    have e11 := in1193_ind_disj d11 z
    have e12 := in1193_ind_disj d12 z
    have e13 := in1193_ind_disj d13 z
    have e14 := in1193_ind_disj d14 z
    have e15 := in1193_ind_disj d15 z
    have e16 := in1193_ind_disj d16 z
    have e17 := in1193_ind_disj d17 z
    have e18 := in1193_ind_disj d18 z
    have e19 := in1193_ind_disj d19 z
    have e20 := in1193_ind_disj d20 z
    have e21 := in1193_ind_disj d21 z
    have hfw := in1193_ind_inter F W z
    rcases in1193_ind_01 Mab z with h1 | h1 <;> rcases in1193_ind_01 Mbc z with h2 | h2 <;>
      rcases in1193_ind_01 Mac z with h3 | h3 <;> rcases in1193_ind_01 F z with h4 | h4 <;>
      rcases in1193_ind_01 W z with h5 | h5 <;> omega
  have hs := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, in1193_ind_sum _ _ s1, in1193_ind_sum _ _ s2,
    in1193_ind_sum _ _ s3, in1193_ind_sum _ _ s4, in1193_ind_sum _ _ s5, in1193_ind_sum _ _ s6,
    in1193_ind_sum _ _ s7, in1193_ind_sum _ _ s8, in1193_ind_sum _ _ s9,
    in1193_ind_sum _ _ (Finset.inter_subset_left.trans s8), Finset.sum_const, Nat.card_Icc,
    smul_eq_mul] at hs
  omega

theorem in1193_no_col (c : Fin 26 → Fin 26 → Finset ℕ)
    (hp : multigraph_is_proper_edge_coloring in1193_G 106 c)
    (hl : multigraph_is_locally_bounded in1193_G c) : False := by
  obtain ⟨hsym, hcard, hrange, hdisj⟩ := hp
  have hsub : ∀ u v, c u v ⊆ Finset.Icc 1 106 := fun u v x hx => Finset.mem_Icc.mpr (hrange u v x hx)
  have hc : ∀ u v, (c u v).card = 21 * in1193_unit u v := hcard
  have key : ∀ i : Fin 5, 17 ≤ (c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2)).card := by
    intro i
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, -⟩ := in1193_facts i
    have ne : ∀ r s : Fin 5, r ≠ s → in1193_v i r ≠ in1193_v i s :=
      fun r s hrs h => hrs (in1193_v_inj i i r s h).2
    have nh : ∀ r : Fin 5, in1193_v i r ≠ in1193_hub := in1193_v_ne_hub i
    have := in1193_gadget 21 106 rfl
      (c (in1193_v i 0) (in1193_v i 1)) (c (in1193_v i 1) (in1193_v i 2)) (c (in1193_v i 0) (in1193_v i 2))
      (c (in1193_v i 0) (in1193_v i 3)) (c (in1193_v i 0) (in1193_v i 4))
      (c (in1193_v i 1) (in1193_v i 3)) (c (in1193_v i 1) (in1193_v i 4))
      (c (in1193_v i 3) (in1193_v i 4)) (c in1193_hub (in1193_v i 2))
      (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _) (hsub _ _)
      (by rw [hc, m1]) (by rw [hc, m2]) (by rw [hc, m3]) (by rw [hc, m4]) (by rw [hc, m5])
      (by rw [hc, m6]) (by rw [hc, m7]) (by rw [hc, m8]) (by rw [hc, m9])
      (by rw [hsym (in1193_v i 0) (in1193_v i 1)]; exact hdisj _ _ _ (ne 0 2 (by decide)))
      (hdisj _ _ _ (ne 1 2 (by decide)))
      (by rw [hsym (in1193_v i 1) (in1193_v i 2), hsym (in1193_v i 0) (in1193_v i 2)]; exact hdisj _ _ _ (ne 1 0 (by decide)))
      (hdisj _ _ _ (ne 1 3 (by decide))) (hdisj _ _ _ (ne 1 4 (by decide)))
      (hdisj _ _ _ (ne 2 3 (by decide))) (hdisj _ _ _ (ne 2 4 (by decide)))
      (hdisj _ _ _ (ne 3 4 (by decide)))
      (by rw [hsym (in1193_v i 0) (in1193_v i 1)]; exact hdisj _ _ _ (ne 0 3 (by decide)))
      (by rw [hsym (in1193_v i 0) (in1193_v i 1)]; exact hdisj _ _ _ (ne 0 4 (by decide)))
      (hdisj _ _ _ (ne 2 3 (by decide))) (hdisj _ _ _ (ne 2 4 (by decide)))
      (hdisj _ _ _ (ne 3 4 (by decide)))
      (by rw [hsym (in1193_v i 1) (in1193_v i 2), hsym in1193_hub (in1193_v i 2)]; exact hdisj _ _ _ (nh 1))
      (by rw [hsym (in1193_v i 0) (in1193_v i 2), hsym in1193_hub (in1193_v i 2)]; exact hdisj _ _ _ (nh 0))
      (by rw [hsym (in1193_v i 0) (in1193_v i 3), hsym (in1193_v i 1) (in1193_v i 3)]; exact hdisj _ _ _ (ne 0 1 (by decide)))
      (by rw [hsym (in1193_v i 0) (in1193_v i 3)]; exact hdisj _ _ _ (ne 0 4 (by decide)))
      (by rw [hsym (in1193_v i 1) (in1193_v i 3)]; exact hdisj _ _ _ (ne 1 4 (by decide)))
      (by rw [hsym (in1193_v i 0) (in1193_v i 4), hsym (in1193_v i 1) (in1193_v i 4)]; exact hdisj _ _ _ (ne 0 1 (by decide)))
      (by rw [hsym (in1193_v i 0) (in1193_v i 4), hsym (in1193_v i 3) (in1193_v i 4)]; exact hdisj _ _ _ (ne 0 3 (by decide)))
      (by rw [hsym (in1193_v i 1) (in1193_v i 4), hsym (in1193_v i 3) (in1193_v i 4)]; exact hdisj _ _ _ (ne 1 3 (by decide)))
    omega
  have hlow : ∀ i : Fin 5, c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2) ⊆ Finset.Icc 1 84 := by
    intro i z hz
    have hz1 := (Finset.mem_inter.mp hz).1
    have hb := hl _ _ z hz1
    rw [(in1193_facts i).2.2.2.2.2.2.2.2.2] at hb
    exact Finset.mem_Icc.mpr ⟨(hrange _ _ z hz1).1, hb⟩
  have hpd : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)), i ≠ j →
      Disjoint (c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2))
        (c (in1193_v j 3) (in1193_v j 4) ∩ c in1193_hub (in1193_v j 2)) := by
    intro i _ j _ hij
    exact (hdisj in1193_hub _ _ (fun h => hij (in1193_v_inj i j 2 2 h).1)).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have h1 := Finset.card_biUnion hpd
  have h2 : ((Finset.univ : Finset (Fin 5)).biUnion
      (fun i => c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2))).card ≤ 84 := by
    have hsubU : ((Finset.univ : Finset (Fin 5)).biUnion
        (fun i => c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2))) ⊆ Finset.Icc 1 84 := by
      intro z hz
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
      exact hlow i hi
    have := Finset.card_le_card hsubU
    simpa using this
  have h3 : ∑ i : Fin 5, 17 ≤ ∑ i : Fin 5, (c (in1193_v i 3) (in1193_v i 4) ∩ c in1193_hub (in1193_v i 2)).card :=
    Finset.sum_le_sum (fun i _ => key i)
  simp at h3
  omega

/-- Open problem OP-2287: existence of a multigraph with local-to-ordinary chromatic index gap at least two. -/
theorem multigraph_local_to_ordinary_chromatic_index_gap_ge_two_exists : ∃ (n : ℕ) (G : Multigraph (Fin n)), multigraph_chromatic_index G + 2 ≤ multigraph_local_chromatic_index G := by
  refine ⟨26, in1193_G, ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := in1193_blocksA
  obtain ⟨b1, b2, b3, b4⟩ := in1193_blocksB
  have hA : multigraph_chromatic_index in1193_G ≤ 105 :=
    Nat.sInf_le ⟨_, in1193_proper_of_blocks _ 5 a1 a2 a3 a4⟩
  have hB : multigraph_is_locally_bounded in1193_G (fun u v => in1193_col (in1193_blk in1193_tB u v)) := by
    intro u v x hx
    obtain ⟨_, b, hb, hx2⟩ := in1193_col_mem _ x hx
    exact hx2.trans (in1193_boundB u v b hb)
  have hne : {k : ℕ | ∃ c : Fin 26 → Fin 26 → Finset ℕ, multigraph_is_proper_edge_coloring in1193_G k c ∧ multigraph_is_locally_bounded in1193_G c}.Nonempty :=
    ⟨126, _, in1193_proper_of_blocks _ 6 b1 b2 b3 b4, hB⟩
  have hC : 107 ≤ multigraph_local_chromatic_index in1193_G := by
    refine le_csInf hne ?_
    rintro k ⟨c, hp, hl⟩
    by_contra hk
    rw [not_le] at hk
    refine in1193_no_col c ⟨hp.1, hp.2.1, fun u v x hx => ?_, hp.2.2.2⟩ hl
    have := hp.2.2.1 u v x hx
    exact ⟨this.1, by omega⟩
  omega
