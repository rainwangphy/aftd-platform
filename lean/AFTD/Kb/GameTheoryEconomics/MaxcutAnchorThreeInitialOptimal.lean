import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityColorPermutation
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.V

/-!
# maxcut_anchor_three_initial_optimal

Topic: equilibria   Node: f72665ac3959

Provenance: formalization of a published result. Source: arXiv:2610.04948, https://arxiv.org/html/2610.04948v1, Section 2, Lemmas 3-5 and Theorem 2 specialized to k=3. The proof uses the anchor-conflict gap and Nash recoloring bounds; after fixing A and B it minimizes C and D independently, checking the remaining 256 binary profiles by kernel decision.

The displayed initial coloring sigma of the 91-vertex graph G_3 in arXiv:2610.04948 maximizes social welfare among all three-colorings.
-/

open scoped BigOperators
namespace MaxcutDegree66Opt

private def mono {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) : ℕ :=
  ∑ v, (Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v).card

private lemma mono_sum {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) :
    mono G ρ = ∑ v, ∑ w, if G.Adj v w ∧ ρ w = ρ v then 1 else 0 := by
  simp only [mono, Finset.card_filter]

private lemma welfare_add_mono {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) :
    maxcut_welfare G ρ + mono G ρ = ∑ v, G.degree v := by
  rw [maxcut_welfare, mono, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => maxcut_utility_add_monochromatic_card G ρ v

private lemma independent_mono_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (ρ : V → Fin k)
    (S : Finset V) (hind : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w) :
    2 * (∑ v ∈ S, (Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v).card)
      ≤ mono G ρ := by
  classical
  let f : V → V → ℕ := fun v w => if G.Adj v w ∧ ρ w = ρ v then 1 else 0
  have hsym (v w : V) : f v w = f w v := by
    dsimp [f]
    congr 1
    exact propext ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hzero : ∑ v ∈ S, ∑ w ∈ S, f v w = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    simp [f, hind v hv w hw]
  have hcross : ∑ v ∈ Sᶜ, ∑ w ∈ S, f v w = ∑ v ∈ S, ∑ w ∈ Sᶜ, f v w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => hsym w v
  have hsplit (v : V) : ∑ w, f v w = ∑ w ∈ S, f v w + ∑ w ∈ Sᶜ, f v w :=
    (Finset.sum_add_sum_compl S _).symm
  have hall : mono G ρ =
      2 * (∑ v ∈ S, ∑ w ∈ Sᶜ, f v w) + ∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, f v w := by
    rw [mono_sum]
    change (∑ v, ∑ w, f v w) = _
    rw [← Finset.sum_add_sum_compl S]
    simp only [hsplit, Finset.sum_add_distrib, hzero, hcross]
    omega
  have hpart : (∑ v ∈ S, (Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v).card) =
      ∑ v ∈ S, ∑ w ∈ Sᶜ, f v w := by
    simp only [Finset.card_filter]
    change (∑ v ∈ S, ∑ w, f v w) = _
    simp only [hsplit, Finset.sum_add_distrib, hzero, zero_add]
  rw [hpart, hall]
  omega

private lemma exists_good_of_independent {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (ρ : V → Fin k)
    (S : Finset V) (hind : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w)
    (hsmall : mono G ρ < 2 * S.card) :
    ∃ v ∈ S, ∀ w, G.Adj v w → ρ w ≠ ρ v := by
  classical
  by_contra h
  push_neg at h
  have hpos : ∀ v ∈ S, 1 ≤ (Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v).card := by
    intro v hv
    obtain ⟨w, hadj, hc⟩ := h v hv
    exact Finset.card_pos.mpr ⟨w, by simp [hadj, hc]⟩
  have hsum := Finset.sum_le_sum hpos
  have hb := independent_mono_bound G ρ S hind
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega


set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

private abbrev V := Fin 16 ⊕ (Fin 3 × Fin 25)
private abbrev G := maxcut_anchor_three_graph

private instance graph_dec : DecidableRel G.Adj := by
  unfold G maxcut_anchor_three_graph
  infer_instance

private lemma anchor_adj (j l : Fin 3) (i t : Fin 25) :
    G.Adj (.inr (j,i)) (.inr (l,t)) ↔ j ≠ l := by
  change ((Sum.inr (j,i) : V) ≠ Sum.inr (l,t) ∧ (j ≠ l ∨ l ≠ j)) ↔ j ≠ l
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    exact h (congrArg Prod.fst (Sum.inr.inj heq))

private lemma initial_mono : mono G maxcut_anchor_three_initial_coloring = 48 := by
  decide

private lemma optimal_mono (ρ : V → Fin 3) (hopt : is_maxcut_optimal G ρ) :
    mono G ρ ≤ 48 := by
  have h := hopt maxcut_anchor_three_initial_coloring
  have hs := welfare_add_mono G maxcut_anchor_three_initial_coloring
  have hr := welfare_add_mono G ρ
  rw [initial_mono] at hs
  omega

private lemma anchor_rigidity (ρ : V → Fin 3) (hsmall : mono G ρ < 50) :
    ∃ p : Equiv.Perm (Fin 3), ∀ j i, ρ (.inr (j,i)) = p j := by
  classical
  have hgood : ∀ j : Fin 3, ∃ i : Fin 25,
      ∀ w, G.Adj (.inr (j,i)) w → ρ w ≠ ρ (.inr (j,i)) := by
    intro j
    let S : Finset V := Finset.univ.image fun i : Fin 25 => Sum.inr (j,i)
    have hcard : S.card = 25 := by
      rw [Finset.card_image_of_injective _ (by intro a b h; simpa using h)]
      decide
    have hind : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w := by
      intro v hv w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      simp [anchor_adj]
    obtain ⟨v, hv, hg⟩ := exists_good_of_independent G ρ S hind (by omega)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i, hg⟩
  choose g hg using hgood
  let c : Fin 3 → Fin 3 := fun j => ρ (.inr (j, g j))
  have hi : Function.Injective c := by
    intro j l heq
    by_contra hne
    exact hg j (.inr (l, g l)) ((anchor_adj j l _ _).2 hne) heq.symm
  have hb : Function.Bijective c := (Fintype.bijective_iff_injective_and_card c).2 ⟨hi, rfl⟩
  refine ⟨Equiv.ofBijective c hb, ?_⟩
  intro j i
  obtain ⟨l, hl⟩ := hb.2 (ρ (.inr (j,i)))
  have heq : l = j := by
    by_contra hne
    exact hg l (.inr (j,i)) ((anchor_adj l j _ _).2 hne) hl.symm
  subst l
  exact hl.symm

private lemma welfare_perm (ρ : V → Fin 3) (p : Equiv.Perm (Fin 3)) :
    maxcut_welfare G (fun v => p (ρ v)) = maxcut_welfare G ρ := by
  simp only [maxcut_welfare, maxcut_utility_color_permutation]

private lemma optimal_perm (ρ : V → Fin 3) (h : is_maxcut_optimal G ρ) (p : Equiv.Perm (Fin 3)) :
    is_maxcut_optimal G (fun v => p (ρ v)) := by
  intro τ
  have hh := h (fun v => p.symm (τ v))
  have ht := welfare_perm (fun v => p.symm (τ v)) p
  simp only [Equiv.apply_symm_apply] at ht
  rw [welfare_perm, ht]
  exact hh

end MaxcutDegree66Opt


open scoped BigOperators
namespace MaxcutDegree66OptCore
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

private abbrev V := Fin 16 ⊕ (Fin 3 × Fin 25)
private abbrev G := maxcut_anchor_three_graph
private instance graph_dec : DecidableRel G.Adj := by
  unfold G maxcut_anchor_three_graph
  infer_instance

private def field (u : Fin 16) (j : Fin 3) : ℕ :=
  match u.val / 4, j.val with
  | 0, 1 => 6
  | 0, 2 => 3
  | 1, 1 => 1
  | 1, 2 => 6
  | 2, 0 => 6
  | 2, 2 => 1
  | 3, 1 => 3
  | 3, 2 => 6
  | _, _ => 0

private def energy (s : Fin 16 → Fin 3) : ℕ :=
  (∑ u, ∑ v, if G.Adj (.inl u) (.inl v) ∧ s v = s u then 1 else 0) +
    2 * ∑ u, field u (s u)

private def A (i : Fin 4) : Fin 16 := ⟨i.val, by omega⟩
private def B (i : Fin 4) : Fin 16 := ⟨4+i.val, by omega⟩
private def C (i : Fin 4) : Fin 16 := ⟨8+i.val, by omega⟩
private def D (i : Fin 4) : Fin 16 := ⟨12+i.val, by omega⟩
private def partner (i : Fin 4) : Fin 4 := ⟨i.val / 2 * 2 + (1 - i.val % 2), by omega⟩

private def base (s : Fin 16 → Fin 3) : ℕ :=
  (∑ i, field (A i) (s (A i))) + (∑ i, field (B i) (s (B i))) +
    ∑ i, ∑ j, if i ≠ j ∧ s (A i) = s (B j) then 1 else 0

private def costC (s : Fin 16 → Fin 3) (i : Fin 4) (c : Fin 3) : ℕ :=
  field (C i) c + (if s (A i) = c then 1 else 0) +
  (if s (B i) = c then 1 else 0) +
  (if s (B (partner i)) = c then 1 else 0)

private def costD (s : Fin 16 → Fin 3) (i : Fin 4) (c : Fin 3) : ℕ :=
  field (D i) c + (∑ j, if s (A j) = c then 1 else 0) +
  ∑ j, if i ≠ j ∧ s (B j) = c then 1 else 0

private def lower (s : Fin 16 → Fin 3) : ℕ :=
  base s + (∑ i, min (costC s i 1) (costC s i 2)) +
    ∑ i, min (costD s i 0) (costD s i 1)

private def profileAB (a b : Fin 4 → Bool) (u : Fin 16) : Fin 3 :=
  let i : Fin 4 := ⟨u.val % 4, Nat.mod_lt _ (by decide)⟩
  if u.val < 4 then (if a i then 0 else 2) else (if b i then 0 else 1)

private lemma certificate : ∀ a b : Fin 4 → Bool, 24 ≤ lower (profileAB a b) := by
  have h : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
      24 ≤ lower (profileAB ![a0,a1,a2,a3] ![b0,b1,b2,b3]) := by
    decide
  intro a b
  have ha : ![a 0,a 1,a 2,a 3] = a := by ext i; fin_cases i <;> rfl
  have hb : ![b 0,b 1,b 2,b 3] = b := by ext i; fin_cases i <;> rfl
  simpa only [ha, hb] using h (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2) (b 3)

private def coreRel (u v : Fin 16) : Prop :=
  (u.val < 4 ∧ 12 ≤ v.val) ∨
  (u.val < 4 ∧ 4 ≤ v.val ∧ v.val < 8 ∧ u.val ≠ v.val - 4) ∨
  (4 ≤ u.val ∧ u.val < 8 ∧ 12 ≤ v.val ∧ u.val - 4 ≠ v.val - 12) ∨
  (u.val < 4 ∧ v.val = u.val + 8) ∨
  (4 ≤ u.val ∧ u.val < 8 ∧
    (v.val = u.val + 4 ∨ v.val = (u.val - 4) / 2 * 2 + (1 - (u.val - 4) % 2) + 8))

private lemma core_adj (u v : Fin 16) :
    G.Adj (.inl u) (.inl v) ↔ u ≠ v ∧ (coreRel u v ∨ coreRel v u) := by
  change ((Sum.inl u : V) ≠ Sum.inl v ∧ (coreRel u v ∨ coreRel v u)) ↔ _
  constructor
  · rintro ⟨hne, hrel⟩
    exact ⟨fun h => hne (congrArg Sum.inl h), hrel⟩
  · rintro ⟨hne, hrel⟩
    exact ⟨fun h => hne (Sum.inl.inj h), hrel⟩

end MaxcutDegree66OptCore


open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 200000
namespace MaxcutDegree66OptCore

private lemma sum_blocks (f : Fin 16 → ℕ) :
    (∑ u, f u) = (∑ i, f (A i)) + (∑ i, f (B i)) +
      (∑ i, f (C i)) + ∑ i, f (D i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (0))))))))))))))))) = (f 0 + (f 1 + (f 2 + (f 3 + (0))))) + (f 4 + (f 5 + (f 6 + (f 7 + (0))))) + (f 8 + (f 9 + (f 10 + (f 11 + (0))))) + (f 12 + (f 13 + (f 14 + (f 15 + (0)))))
  omega

private def cross (s : Fin 16 → Fin 3) (X Y : Fin 4 → Fin 16) : ℕ :=
  ∑ i, ∑ j, if G.Adj (.inl (X i)) (.inl (Y j)) ∧ s (Y j) = s (X i) then 1 else 0

private lemma cross_symm (s : Fin 16 → Fin 3) (X Y : Fin 4 → Fin 16) :
    cross s X Y = cross s Y X := by
  unfold cross
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact propext ⟨fun h => ⟨h.1.symm,h.2.symm⟩,fun h => ⟨h.1.symm,h.2.symm⟩⟩

private lemma diag_zero (s : Fin 16 → Fin 3) :
    cross s A A = 0 ∧ cross s B B = 0 ∧ cross s C C = 0 ∧ cross s D D = 0 := by
  have ha : ∀ i j : Fin 4, ¬ G.Adj (.inl (A i)) (.inl (A j)) := by decide
  have hb : ∀ i j : Fin 4, ¬ G.Adj (.inl (B i)) (.inl (B j)) := by decide
  have hc : ∀ i j : Fin 4, ¬ G.Adj (.inl (C i)) (.inl (C j)) := by decide
  have hd : ∀ i j : Fin 4, ¬ G.Adj (.inl (D i)) (.inl (D j)) := by decide
  simp [cross,ha,hb,hc,hd]

private lemma cd_zero (s : Fin 16 → Fin 3) : cross s C D = 0 := by
  have h : ∀ i j : Fin 4, ¬ G.Adj (.inl (C i)) (.inl (D j)) := by decide
  simp [cross,h]

private lemma raw_decomp (s : Fin 16 → Fin 3) :
    (∑ u, ∑ v, if G.Adj (.inl u) (.inl v) ∧ s v = s u then 1 else 0) =
      2 * (cross s A B + cross s A C + cross s A D + cross s B C + cross s B D) := by
  rw [sum_blocks]
  simp only [sum_blocks,Finset.sum_add_distrib]
  change cross s A A + cross s A B + cross s A C + cross s A D +
    (cross s B A + cross s B B + cross s B C + cross s B D) +
    (cross s C A + cross s C B + cross s C C + cross s C D) +
    (cross s D A + cross s D B + cross s D C + cross s D D) = _
  obtain ⟨ha,hb,hc,hd⟩ := diag_zero s
  rw [cross_symm s B A,cross_symm s C A,cross_symm s C B,
    cross_symm s D A,cross_symm s D B,cross_symm s D C]
  simp only [ha,hb,hc,hd,cd_zero]
  omega

private lemma base_eq (s : Fin 16 → Fin 3) :
    base s = (∑ i, field (A i) (s (A i))) + (∑ i, field (B i) (s (B i))) + cross s A B := by
  have h : ∀ i j : Fin 4, G.Adj (.inl (A i)) (.inl (B j)) ↔ i ≠ j := by decide
  simp only [base,cross,h,eq_comm]

private def incost (s : Fin 16 → Fin 3) (X : Fin 4 → Fin 16) (v : Fin 16) : ℕ :=
  ∑ j, if G.Adj (.inl (X j)) (.inl v) ∧ s v = s (X j) then 1 else 0

private lemma sum_incost (s : Fin 16 → Fin 3) (X Y : Fin 4 → Fin 16) :
    (∑ i, incost s X (Y i)) = cross s X Y := by
  unfold incost cross
  exact Finset.sum_comm

private lemma costC_eq (s : Fin 16 → Fin 3) (i : Fin 4) :
    costC s i (s (C i)) = field (C i) (s (C i)) + incost s A (C i) + incost s B (C i) := by
  have hac : ∀ i j : Fin 4, G.Adj (.inl (A j)) (.inl (C i)) ↔ j = i := by decide
  have hbc : ∀ i j : Fin 4, G.Adj (.inl (B j)) (.inl (C i)) ↔ j = i ∨ j = partner i := by decide
  have hp : ∀ i : Fin 4, i ≠ partner i := by decide
  have hor (j : Fin 4) :
      (if (j = i ∨ j = partner i) ∧ s (C i) = s (B j) then 1 else 0 : ℕ) =
      (if j = i ∧ s (C i) = s (B j) then 1 else 0) +
      (if j = partner i ∧ s (C i) = s (B j) then 1 else 0) := by
    by_cases h : j = i
    · subst j
      simp [hp]
    · simp [h]
  unfold incost
  simp only [hac,hbc,hor,Finset.sum_add_distrib,ite_and]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [costC,eq_comm]
  omega

private lemma costD_eq (s : Fin 16 → Fin 3) (i : Fin 4) :
    costD s i (s (D i)) = field (D i) (s (D i)) + incost s A (D i) + incost s B (D i) := by
  have had : ∀ i j : Fin 4, G.Adj (.inl (A j)) (.inl (D i)) := by decide
  have hbd : ∀ i j : Fin 4, G.Adj (.inl (B j)) (.inl (D i)) ↔ i ≠ j := by decide
  simp only [costD,incost,had,hbd,true_and,eq_comm]

private lemma sumC (s : Fin 16 → Fin 3) :
    (∑ i, costC s i (s (C i))) = (∑ i, field (C i) (s (C i))) + cross s A C + cross s B C := by
  simp_rw [costC_eq]
  simp only [Finset.sum_add_distrib,sum_incost]

private lemma sumD (s : Fin 16 → Fin 3) :
    (∑ i, costD s i (s (D i))) = (∑ i, field (D i) (s (D i))) + cross s A D + cross s B D := by
  simp_rw [costD_eq]
  simp only [Finset.sum_add_distrib,sum_incost]

private lemma energy_decomp (s : Fin 16 → Fin 3) :
    energy s = 2 * (base s + (∑ i, costC s i (s (C i))) + ∑ i, costD s i (s (D i))) := by
  unfold energy
  rw [raw_decomp,sum_blocks,base_eq,sumC,sumD]
  ring

end MaxcutDegree66OptCore

open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 200000
namespace MaxcutDegree66OptFinal
open MaxcutDegree66OptCore
private abbrev V := MaxcutDegree66Opt.V
private abbrev G := MaxcutDegree66Opt.G


private def allowed (u : Fin 16) (c : Fin 3) : Prop :=
  if u.val < 4 then c = 0 ∨ c = 2 else
  if u.val < 8 then c = 0 ∨ c = 1 else
  if u.val < 12 then c = 1 ∨ c = 2 else c = 0 ∨ c = 1

private def dcore (u : Fin 16) : ℕ := if u.val < 8 then 8 else if u.val < 12 then 3 else 7

private def coreCount (s : Fin 16 → Fin 3) (u : Fin 16) (c : Fin 3) : ℕ :=
  ∑ v, if G.Adj (.inl u) (.inl v) ∧ s v = c then 1 else 0

private lemma degree_core : ∀ u : Fin 16,
    (∑ v : Fin 16, if G.Adj (.inl u) (.inl v) then 1 else 0) = dcore u := by
  decide

private lemma anchor_cost : ∀ (u : Fin 16) (c : Fin 3),
    (∑ w : Fin 3 × Fin 25, if G.Adj (.inl u) (.inr w) ∧ w.1 = c then 1 else 0) =
      field u c := by
  decide


private lemma count_canonical (ρ : V → Fin 3)
    (hc : ∀ j i, ρ (.inr (j,i)) = j) (u : Fin 16) (c : Fin 3) :
    (Finset.univ.filter fun w => G.Adj (.inl u) w ∧ ρ w = c).card =
      coreCount (fun v => ρ (.inl v)) u c + field u c := by
  have hcanon (w : Fin 3 × Fin 25) : ρ (.inr w) = w.1 := hc _ _
  simp only [Finset.card_filter, Fintype.sum_sum_type, hcanon]
  exact congrArg (fun x => coreCount (fun v => ρ (.inl v)) u c + x) (anchor_cost u c)


private lemma count_sum (s : Fin 16 → Fin 3) (u : Fin 16) :
    (∑ c : Fin 3, coreCount s u c) = dcore u := by
  simp only [coreCount]
  rw [Finset.sum_comm]
  have ht (v : Fin 16) :
      (∑ c : Fin 3, if G.Adj (.inl u) (.inl v) ∧ s v = c then 1 else 0) =
        (if G.Adj (.inl u) (.inl v) then 1 else 0) := by
    by_cases h : G.Adj (.inl u) (.inl v) <;> simp [h]
  simp_rw [ht]
  exact degree_core u


private lemma allowed_of_nash (u : Fin 16) (c : Fin 3) (x : Fin 3 → ℕ)
    (hsum : ∑ d, x d = dcore u)
    (h : ∀ d, x c + field u c ≤ x d + field u d) : allowed u c := by
  have cert : ∀ (u : Fin 16) (c : Fin 3), ¬ allowed u c →
      field u c = 6 ∧ ∃ a b : Fin 3, a ≠ b ∧ dcore u + field u a + field u b ≤ 11 := by
    unfold allowed dcore field
    decide
  by_contra hc
  obtain ⟨hc,a,b,hab,hbound⟩ := cert u c hc
  have habsum : x a + x b ≤ dcore u := by
    calc
      x a + x b = ∑ d ∈ ({a,b} : Finset (Fin 3)), x d := (Finset.sum_pair hab).symm
      _ ≤ ∑ d : Fin 3, x d := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = dcore u := hsum
  have ha := h a
  have hb := h b
  rw [hc] at ha hb
  omega


private lemma optimal_allowed (ρ : V → Fin 3) (hopt : is_maxcut_optimal G ρ)
    (hc : ∀ j i, ρ (.inr (j,i)) = j) : ∀ u, allowed u (ρ (.inl u)) := by
  intro u
  apply allowed_of_nash u (ρ (.inl u)) (coreCount (fun v => ρ (.inl v)) u)
  · exact count_sum _ _
  · intro c
    have h := maxcut_optimal_same_color_le G ρ hopt (.inl u) c
    rwa [count_canonical ρ hc u (ρ (.inl u)), count_canonical ρ hc u c] at h


private lemma mono_energy (ρ : V → Fin 3) (hc : ∀ j i, ρ (.inr (j,i)) = j) :
    MaxcutDegree66Opt.mono G ρ = energy (fun u => ρ (.inl u)) := by
  let f : V → V → ℕ := fun v w => if G.Adj v w ∧ ρ w = ρ v then 1 else 0
  have hsym (v w : V) : f v w = f w v := by
    dsimp [f]
    congr 1
    exact propext ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hcanon (w : Fin 3 × Fin 25) : ρ (.inr w) = w.1 := hc _ _
  have hca (u : Fin 16) : (∑ w : Fin 3 × Fin 25, f (.inl u) (.inr w)) =
      field u (ρ (.inl u)) := by
    simp only [f, hcanon]
    exact anchor_cost u (ρ (.inl u))
  have hac : (∑ w : Fin 3 × Fin 25, ∑ u : Fin 16, f (.inr w) (.inl u)) =
      ∑ u : Fin 16, field u (ρ (.inl u)) := by
    rw [Finset.sum_comm]
    simp_rw [hsym, hca]
  have haa (w z : Fin 3 × Fin 25) : f (.inr w) (.inr z) = 0 := by
    rcases w with ⟨j,i⟩
    rcases z with ⟨l,t⟩
    simp [f, hcanon, MaxcutDegree66Opt.anchor_adj, eq_comm]
  rw [MaxcutDegree66Opt.mono_sum]
  change (∑ v : V, ∑ w : V, f v w) = _
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, hca, hac, haa,
    Finset.sum_const_zero, add_zero]
  dsimp [energy, f]
  ring


private lemma lower_congr (s t : Fin 16 → Fin 3)
    (h : ∀ u, u.val < 8 → s u = t u) : lower s = lower t := by
  have ha (i : Fin 4) : s (A i) = t (A i) := h _ (by dsimp [A]; omega)
  have hb (i : Fin 4) : s (B i) = t (B i) := h _ (by dsimp [B]; omega)
  simp only [lower, base, costC, costD, ha, hb]


private lemma restricted_bound (s : Fin 16 → Fin 3) (hs : ∀ u, allowed u (s u)) :
    48 ≤ energy s := by
  classical
  let a : Fin 4 → Bool := fun i => decide (s (A i) = 0)
  let b : Fin 4 → Bool := fun i => decide (s (B i) = 0)
  have hp0 : s (0 : Fin 16) = profileAB a b 0 := by
    have hh : s (0 : Fin 16) = 0 ∨ s 0 = 2 := hs 0
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp1 : s (1 : Fin 16) = profileAB a b 1 := by
    have hh : s (1 : Fin 16) = 0 ∨ s 1 = 2 := hs 1
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp2 : s (2 : Fin 16) = profileAB a b 2 := by
    have hh : s (2 : Fin 16) = 0 ∨ s 2 = 2 := hs 2
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp3 : s (3 : Fin 16) = profileAB a b 3 := by
    have hh : s (3 : Fin 16) = 0 ∨ s 3 = 2 := hs 3
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp4 : s (4 : Fin 16) = profileAB a b 4 := by
    have hh : s (4 : Fin 16) = 0 ∨ s 4 = 1 := hs 4
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp5 : s (5 : Fin 16) = profileAB a b 5 := by
    have hh : s (5 : Fin 16) = 0 ∨ s 5 = 1 := hs 5
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp6 : s (6 : Fin 16) = profileAB a b 6 := by
    have hh : s (6 : Fin 16) = 0 ∨ s 6 = 1 := hs 6
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hp7 : s (7 : Fin 16) = profileAB a b 7 := by
    have hh : s (7 : Fin 16) = 0 ∨ s 7 = 1 := hs 7
    rcases hh with hh | hh
    all_goals simp [profileAB,a,b,A,B,Fin.reduceFinMk,hh]
  have hab : ∀ u, u.val < 8 → s u = profileAB a b u := by
    intro u hu
    fin_cases u <;> norm_num [Fin.reduceFinMk] at hu
    all_goals first | exact hp0 | exact hp1 | exact hp2 | exact hp3 | exact hp4 | exact hp5 | exact hp6 | exact hp7
  have hmin : 24 ≤ lower s := by
    rw [lower_congr s (profileAB a b) hab]
    exact certificate a b
  have hC : (∑ i, min (costC s i 1) (costC s i 2)) ≤
      ∑ i, costC s i (s (C i)) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := hs (C i)
    have hh' : s (C i) = 1 ∨ s (C i) = 2 := by
      simpa [allowed, C, show ¬ 8+i.val < 4 by omega, show ¬ 8+i.val < 8 by omega,
        show 8+i.val < 12 by omega] using hh
    rcases hh' with h | h
    · rw [h]; exact min_le_left _ _
    · rw [h]; exact min_le_right _ _
  have hD : (∑ i, min (costD s i 0) (costD s i 1)) ≤
      ∑ i, costD s i (s (D i)) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := hs (D i)
    have hh' : s (D i) = 0 ∨ s (D i) = 1 := by
      simpa [allowed, D, show ¬ 12+i.val < 4 by omega, show ¬ 12+i.val < 8 by omega,
        show ¬ 12+i.val < 12 by omega] using hh
    rcases hh' with h | h
    · rw [h]; exact min_le_left _ _
    · rw [h]; exact min_le_right _ _
  rw [energy_decomp]
  dsimp [lower] at hmin
  omega

end MaxcutDegree66OptFinal


open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
namespace MaxcutDegree66OptFinal
private lemma initial_optimal : is_maxcut_optimal G maxcut_anchor_three_initial_coloring := by
  classical
  let P : ℕ → Prop := fun n => ∃ ρ : V → Fin 3, MaxcutDegree66Opt.mono G ρ = n
  have hex : ∃ n, P n := ⟨48, maxcut_anchor_three_initial_coloring, MaxcutDegree66Opt.initial_mono⟩
  obtain ⟨ρ, hρ⟩ := Nat.find_spec hex
  have hmin (τ : V → Fin 3) : MaxcutDegree66Opt.mono G ρ ≤ MaxcutDegree66Opt.mono G τ := by
    rw [hρ]
    exact Nat.find_min' hex ⟨τ, rfl⟩
  have hopt : is_maxcut_optimal G ρ := by
    intro τ
    have hm := hmin τ
    have h1 := MaxcutDegree66Opt.welfare_add_mono G ρ
    have h2 := MaxcutDegree66Opt.welfare_add_mono G τ
    omega
  obtain ⟨p, hp⟩ := MaxcutDegree66Opt.anchor_rigidity ρ (by have := MaxcutDegree66Opt.optimal_mono ρ hopt; omega)
  let θ : V → Fin 3 := fun v => p.symm (ρ v)
  have htopt : is_maxcut_optimal G θ := MaxcutDegree66Opt.optimal_perm ρ hopt p.symm
  have htcanon : ∀ j i, θ (.inr (j,i)) = j := by
    intro j i
    simp [θ, hp]
  have hlow := restricted_bound (fun u => θ (.inl u)) (optimal_allowed θ htopt htcanon)
  have hm : MaxcutDegree66Opt.mono G θ = 48 := by
    rw [← mono_energy θ htcanon] at hlow
    have hupper : MaxcutDegree66Opt.mono G θ ≤ 48 := MaxcutDegree66Opt.optimal_mono θ htopt
    change 48 ≤ MaxcutDegree66Opt.mono G θ at hlow
    omega
  have ht := MaxcutDegree66Opt.welfare_add_mono G θ
  have hi := MaxcutDegree66Opt.welfare_add_mono G maxcut_anchor_three_initial_coloring
  rw [hm] at ht
  rw [MaxcutDegree66Opt.initial_mono] at hi
  intro τ
  have hh := htopt τ
  omega

end MaxcutDegree66OptFinal

theorem maxcut_anchor_three_initial_optimal :
    @is_maxcut_optimal _ _ maxcut_anchor_three_graph
      (by unfold maxcut_anchor_three_graph; infer_instance) 3
      maxcut_anchor_three_initial_coloring := by
  exact MaxcutDegree66OptFinal.initial_optimal
