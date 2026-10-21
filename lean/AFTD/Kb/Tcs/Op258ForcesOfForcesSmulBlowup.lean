import AFTD.Prelude
import AFTD.Kb.Tcs.Op258BoundedExtension
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258ForcesMonoClique
import AFTD.Kb.Tcs.Op258ChooseTwoMulSqLe
import AFTD.Kb.Tcs.Op258PigeonholeBlocks
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.Tcs.F

/-!
# op_258_forces_of_forces_smul_blowup

Topic: combinatorics   Node: f5ee5fe5479e

Provenance: helper lemma. step towards op_258_forces_step

For γ ≥ 1 and k ≥ 1: if a forces a monochromatic K_{γk}, then the profile γ·a forces a monochromatic K_k.
-/

def op_258_forces_of_forces_smul_blowup_b (γ n : ℕ) : Fin (γ * n) → Fin γ :=
  fun x => (finProdFinEquiv (m := γ) (n := n)).symm x |>.1
def op_258_forces_of_forces_smul_blowup_q (γ n : ℕ) : Fin (γ * n) → Fin n :=
  fun x => (finProdFinEquiv (m := γ) (n := n)).symm x |>.2
def op_258_forces_of_forces_smul_blowup_emb (γ n : ℕ) (r : Fin γ) : Fin n → Fin (γ * n) :=
  fun u => finProdFinEquiv (r, u)
lemma op_258_forces_of_forces_smul_blowup_b_emb (γ n : ℕ) (r : Fin γ) (u : Fin n) :
    op_258_forces_of_forces_smul_blowup_b γ n (op_258_forces_of_forces_smul_blowup_emb γ n r u) = r := by
  simp [op_258_forces_of_forces_smul_blowup_b, op_258_forces_of_forces_smul_blowup_emb]
lemma op_258_forces_of_forces_smul_blowup_q_emb (γ n : ℕ) (r : Fin γ) (u : Fin n) :
    op_258_forces_of_forces_smul_blowup_q γ n (op_258_forces_of_forces_smul_blowup_emb γ n r u) = u := by
  simp [op_258_forces_of_forces_smul_blowup_q, op_258_forces_of_forces_smul_blowup_emb]
lemma op_258_forces_of_forces_smul_blowup_emb_bq (γ n : ℕ) (x : Fin (γ * n)) :
    op_258_forces_of_forces_smul_blowup_emb γ n (op_258_forces_of_forces_smul_blowup_b γ n x) (op_258_forces_of_forces_smul_blowup_q γ n x) = x := by
  simp only [op_258_forces_of_forces_smul_blowup_b, op_258_forces_of_forces_smul_blowup_q, op_258_forces_of_forces_smul_blowup_emb]
  exact Equiv.apply_symm_apply _ _
lemma op_258_forces_of_forces_smul_blowup_eq_of_bq (γ n : ℕ) {x y : Fin (γ * n)}
    (hb : op_258_forces_of_forces_smul_blowup_b γ n x = op_258_forces_of_forces_smul_blowup_b γ n y)
    (hq : op_258_forces_of_forces_smul_blowup_q γ n x = op_258_forces_of_forces_smul_blowup_q γ n y) : x = y := by
  rw [← op_258_forces_of_forces_smul_blowup_emb_bq γ n x, ← op_258_forces_of_forces_smul_blowup_emb_bq γ n y, hb, hq]
lemma op_258_forces_of_forces_smul_blowup_mem_edgeSet_iff (V : Type*) (z : Sym2 V) :
    z ∈ (SimpleGraph.completeGraph V).edgeSet ↔ ¬ z.IsDiag := by
  rw [SimpleGraph.completeGraph_eq_top, SimpleGraph.edgeSet_top]; simp
lemma op_258_forces_of_forces_smul_blowup_emb_injective (γ n : ℕ) (r : Fin γ) :
    Function.Injective (op_258_forces_of_forces_smul_blowup_emb γ n r) := by
  intro u v h
  have := congrArg (fun x => (finProdFinEquiv (m := γ) (n := n)).symm x) h
  simpa [op_258_forces_of_forces_smul_blowup_emb] using this
lemma op_258_forces_of_forces_smul_blowup_mk_mem (n : ℕ) {x y : Fin n} (h : x ≠ y) :
    Sym2.mk x y ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet := by
  rw [op_258_forces_of_forces_smul_blowup_mem_edgeSet_iff, Sym2.mk_isDiag_iff]; exact h
noncomputable def op_258_forces_of_forces_smul_blowup_g (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (x y : Fin (γ * n)) : ℕ+ :=
  if h : op_258_forces_of_forces_smul_blowup_b γ n x = op_258_forces_of_forces_smul_blowup_b γ n y ∧
      op_258_forces_of_forces_smul_blowup_q γ n x ≠ op_258_forces_of_forces_smul_blowup_q γ n y then
    c ⟨Sym2.mk (op_258_forces_of_forces_smul_blowup_q γ n x) (op_258_forces_of_forces_smul_blowup_q γ n y),
        op_258_forces_of_forces_smul_blowup_mk_mem n h.2⟩
  else 1
lemma op_258_forces_of_forces_smul_blowup_g_symm (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) :
    ∀ x y, op_258_forces_of_forces_smul_blowup_g γ n c x y = op_258_forces_of_forces_smul_blowup_g γ n c y x := by
  intro x y
  unfold op_258_forces_of_forces_smul_blowup_g
  by_cases h : op_258_forces_of_forces_smul_blowup_b γ n x = op_258_forces_of_forces_smul_blowup_b γ n y ∧
      op_258_forces_of_forces_smul_blowup_q γ n x ≠ op_258_forces_of_forces_smul_blowup_q γ n y
  · have h' : op_258_forces_of_forces_smul_blowup_b γ n y = op_258_forces_of_forces_smul_blowup_b γ n x ∧
        op_258_forces_of_forces_smul_blowup_q γ n y ≠ op_258_forces_of_forces_smul_blowup_q γ n x :=
      ⟨h.1.symm, fun e => h.2 e.symm⟩
    rw [dif_pos h, dif_pos h']
    congr 1
    apply Subtype.ext
    exact Sym2.eq_iff.2 (Or.inr ⟨rfl, rfl⟩)
  · have h' : ¬ (op_258_forces_of_forces_smul_blowup_b γ n y = op_258_forces_of_forces_smul_blowup_b γ n x ∧
        op_258_forces_of_forces_smul_blowup_q γ n y ≠ op_258_forces_of_forces_smul_blowup_q γ n x) :=
      fun e => h ⟨e.1.symm, fun e2 => e.2 e2.symm⟩
    rw [dif_neg h, dif_neg h']
noncomputable def op_258_forces_of_forces_smul_blowup_lift (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) : Sym2 (Fin (γ * n)) → ℕ+ :=
  Sym2.lift ⟨op_258_forces_of_forces_smul_blowup_g γ n c, op_258_forces_of_forces_smul_blowup_g_symm γ n c⟩
lemma op_258_forces_of_forces_smul_blowup_lift_mk (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (x y : Fin (γ * n)) :
    op_258_forces_of_forces_smul_blowup_lift γ n c (Sym2.mk x y) = op_258_forces_of_forces_smul_blowup_g γ n c x y :=
  Sym2.lift_mk _ x y
lemma op_258_forces_of_forces_smul_blowup_lift_map (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) (r : Fin γ) (z : Sym2 (Fin n))
    (hz : z ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet) :
    op_258_forces_of_forces_smul_blowup_lift γ n c (Sym2.map (op_258_forces_of_forces_smul_blowup_emb γ n r) z) = c ⟨z, hz⟩ := by
  induction z using Sym2.inductionOn with
  | hf u v =>
    have huv : u ≠ v := by
      have h := hz; rw [op_258_forces_of_forces_smul_blowup_mem_edgeSet_iff, Sym2.mk_isDiag_iff] at h; exact h
    rw [Sym2.map_mk, op_258_forces_of_forces_smul_blowup_lift_mk]
    unfold op_258_forces_of_forces_smul_blowup_g
    rw [dif_pos ⟨by rw [op_258_forces_of_forces_smul_blowup_b_emb, op_258_forces_of_forces_smul_blowup_b_emb],
                   by rw [op_258_forces_of_forces_smul_blowup_q_emb, op_258_forces_of_forces_smul_blowup_q_emb]; exact huv⟩]
    congr 1
    apply Subtype.ext
    simp only [op_258_forces_of_forces_smul_blowup_q_emb]
noncomputable def op_258_forces_of_forces_smul_blowup_c0 (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (e : (SimpleGraph.completeGraph (Fin (γ * n))).edgeSet) : ℕ+ :=
  op_258_forces_of_forces_smul_blowup_lift γ n c e.1
noncomputable def op_258_forces_of_forces_smul_blowup_push (γ n : ℕ)
    (p : Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet) :
    (SimpleGraph.completeGraph (Fin (γ * n))).edgeSet :=
  ⟨Sym2.map (op_258_forces_of_forces_smul_blowup_emb γ n p.1) p.2.1, by
    have hz : ¬ p.2.1.IsDiag := by
      have := p.2.2; rwa [op_258_forces_of_forces_smul_blowup_mem_edgeSet_iff] at this
    rw [op_258_forces_of_forces_smul_blowup_mem_edgeSet_iff, Sym2.isDiag_map (op_258_forces_of_forces_smul_blowup_emb_injective γ n p.1)]
    exact hz⟩
lemma op_258_forces_of_forces_smul_blowup_c0_push (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (p : Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet) :
    op_258_forces_of_forces_smul_blowup_c0 γ n c (op_258_forces_of_forces_smul_blowup_push γ n p) = c p.2 := by
  obtain ⟨r, ⟨z, hz⟩⟩ := p
  exact op_258_forces_of_forces_smul_blowup_lift_map γ n c r z hz
lemma op_258_forces_of_forces_smul_blowup_c0_mk (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) {x y : Fin (γ * n)} (hxy : x ≠ y) :
    op_258_forces_of_forces_smul_blowup_c0 γ n c ⟨Sym2.mk x y, op_258_forces_of_forces_smul_blowup_mk_mem (γ * n) hxy⟩
      = op_258_forces_of_forces_smul_blowup_g γ n c x y := by
  simp only [op_258_forces_of_forces_smul_blowup_c0, op_258_forces_of_forces_smul_blowup_lift_mk]
lemma op_258_forces_of_forces_smul_blowup_c0_internal (γ n : ℕ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) {x y : Fin (γ * n)}
    (hb : op_258_forces_of_forces_smul_blowup_b γ n x = op_258_forces_of_forces_smul_blowup_b γ n y)
    (hq : op_258_forces_of_forces_smul_blowup_q γ n x ≠ op_258_forces_of_forces_smul_blowup_q γ n y) (hxy : x ≠ y) :
    op_258_forces_of_forces_smul_blowup_c0 γ n c ⟨Sym2.mk x y, op_258_forces_of_forces_smul_blowup_mk_mem (γ * n) hxy⟩
      = c ⟨Sym2.mk (op_258_forces_of_forces_smul_blowup_q γ n x) (op_258_forces_of_forces_smul_blowup_q γ n y),
            op_258_forces_of_forces_smul_blowup_mk_mem n hq⟩ := by
  rw [op_258_forces_of_forces_smul_blowup_c0_mk γ n c hxy]
  unfold op_258_forces_of_forces_smul_blowup_g
  rw [dif_pos ⟨hb, hq⟩]
lemma op_258_forces_of_forces_smul_blowup_card_bound (γ n : ℕ) (a : ℕ+ → ℝ) (hγ : 1 ≤ γ)
    (hpos : ∀ i, 0 < a i) (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (hc : op_258_bounded (fun i => (γ : ℝ) * a i) n c) (i : ℕ+) :
    ((((Finset.univ : Finset (Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet)).image
        (op_258_forces_of_forces_smul_blowup_push γ n)).filter
          (fun e => op_258_forces_of_forces_smul_blowup_c0 γ n c e = i)).card : ℝ)
      ≤ a i * (((γ * n).choose 2) : ℝ) := by
  classical
  set F : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet :=
    (Finset.univ.filter (fun e => c e = i)) with hFdef
  set T : Finset (Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet) :=
    (Finset.univ.filter (fun p => c p.2 = i)) with hTdef
  set A : Finset (SimpleGraph.completeGraph (Fin (γ * n))).edgeSet :=
    ((Finset.univ : Finset (Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet)).image
        (op_258_forces_of_forces_smul_blowup_push γ n)).filter
          (fun e => op_258_forces_of_forces_smul_blowup_c0 γ n c e = i) with hAdef
  have hT : T = (Finset.univ : Finset (Fin γ)).product F := by
    ext p; simp [hTdef, hFdef]
  have hTcard : T.card = γ * F.card := by
    rw [hT]; simp
  have hsub : A ⊆ T.image (op_258_forces_of_forces_smul_blowup_push γ n) := by
    intro e he
    rw [hAdef] at he
    simp only [Finset.mem_filter, Finset.mem_image] at he
    obtain ⟨p, -, hp⟩ := he.1
    refine Finset.mem_image.mpr ⟨p, ?_, hp⟩
    rw [hTdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← op_258_forces_of_forces_smul_blowup_c0_push γ n c p, hp]
    exact he.2
  have hcardle : A.card ≤ T.card := by
    calc A.card ≤ (T.image (op_258_forces_of_forces_smul_blowup_push γ n)).card := Finset.card_le_card hsub
      _ ≤ T.card := Finset.card_image_le
  have hfib : (F.card : ℝ) ≤ (γ : ℝ) * a i * (n.choose 2 : ℝ) := by
    have hci := hc i
    rw [← hFdef] at hci
    simpa using hci
  have h1 : (A.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcardle
  have h2 : (T.card : ℝ) = (γ : ℝ) * (F.card : ℝ) := by
    rw [hTcard]; push_cast; ring
  have hchoose := op_258_choose_two_mul_sq_le γ n hγ
  have hcast : ((γ ^ 2 * n.choose 2 : ℕ) : ℝ) = (γ : ℝ) ^ 2 * (n.choose 2 : ℝ) := by
    push_cast; ring
  calc (A.card : ℝ)
      ≤ (T.card : ℝ) := h1
    _ = (γ : ℝ) * (F.card : ℝ) := h2
    _ ≤ (γ : ℝ) * ((γ : ℝ) * a i * (n.choose 2 : ℝ)) := by gcongr
    _ = a i * ((γ : ℝ) ^ 2 * (n.choose 2 : ℝ)) := by ring
    _ = a i * ((γ ^ 2 * n.choose 2 : ℕ) : ℝ) := by rw [hcast]
    _ ≤ a i * (((γ * n).choose 2) : ℝ) :=
        mul_le_mul_of_nonneg_left hchoose (hpos i).le

/-- Forcing scales up: if a forces K_{γk} then γ·a forces K_k (one half of Proposition 1.2). -/
theorem op_258_forces_of_forces_smul_blowup (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (hsum : 1 < ∑' i : ℕ+, ENNReal.ofReal (a i)) (γ k : ℕ) (hγ : 1 ≤ γ)
    (h : op_258_forces a (γ * k)) : op_258_forces (fun i => (γ : ℝ) * a i) k := by
  classical
  obtain ⟨n₀, hn₀⟩ := h
  obtain ⟨n₁, hn₁⟩ := op_258_bounded_extension a hpos hanti hsum
  refine ⟨max n₁ n₀, ?_⟩
  intro n hn c hc
  by_contra hno
  have hge : n ≤ γ * n := by
    calc n = 1 * n := (Nat.one_mul n).symm
      _ ≤ γ * n := Nat.mul_le_mul_right n hγ
  have hnN₁ : n₁ ≤ γ * n := le_trans (le_trans (le_max_left n₁ n₀) hn) hge
  have hnN₀ : n₀ ≤ γ * n := le_trans (le_trans (le_max_right n₁ n₀) hn) hge
  obtain ⟨c', hc'bound, hc'agree⟩ :=
    hn₁ (γ * n) hnN₁
      ((Finset.univ : Finset (Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet)).image
        (op_258_forces_of_forces_smul_blowup_push γ n))
      (op_258_forces_of_forces_smul_blowup_c0 γ n c)
      (fun i => op_258_forces_of_forces_smul_blowup_card_bound γ n a hγ hpos c hc i)
  obtain ⟨S, i, hScard, hSmono⟩ := hn₀ (γ * n) hnN₀ c' hc'bound
  obtain ⟨r, hr⟩ := op_258_pigeonhole_blocks S γ k hγ (op_258_forces_of_forces_smul_blowup_b γ n) (by rw [hScard])
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hr
  refine hno ⟨t.image (op_258_forces_of_forces_smul_blowup_q γ n), i, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, ht_card]
    intro x hx y hy hq
    have hbx : op_258_forces_of_forces_smul_blowup_b γ n x = r := (Finset.mem_filter.mp (ht_sub hx)).2
    have hby : op_258_forces_of_forces_smul_blowup_b γ n y = r := (Finset.mem_filter.mp (ht_sub hy)).2
    exact op_258_forces_of_forces_smul_blowup_eq_of_bq γ n (hbx.trans hby.symm) hq
  · intro u v hu hv huv
    simp only [Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    have hxS : x ∈ S := (Finset.mem_filter.mp (ht_sub hx)).1
    have hyS : y ∈ S := (Finset.mem_filter.mp (ht_sub hy)).1
    have hbx : op_258_forces_of_forces_smul_blowup_b γ n x = r := (Finset.mem_filter.mp (ht_sub hx)).2
    have hby : op_258_forces_of_forces_smul_blowup_b γ n y = r := (Finset.mem_filter.mp (ht_sub hy)).2
    have hxy : x ≠ y := by intro e; exact huv (by rw [e])
    have hmono' : c' ⟨Sym2.mk x y, op_258_forces_of_forces_smul_blowup_mk_mem (γ * n) hxy⟩ = i :=
      hSmono hxS hyS hxy
    have hmem : (⟨Sym2.mk x y, op_258_forces_of_forces_smul_blowup_mk_mem (γ * n) hxy⟩ :
          (SimpleGraph.completeGraph (Fin (γ * n))).edgeSet) ∈
        ((Finset.univ : Finset (Fin γ × (SimpleGraph.completeGraph (Fin n)).edgeSet)).image
          (op_258_forces_of_forces_smul_blowup_push γ n)) := by
      apply Finset.mem_image.mpr
      refine ⟨(r, ⟨Sym2.mk (op_258_forces_of_forces_smul_blowup_q γ n x) (op_258_forces_of_forces_smul_blowup_q γ n y),
        op_258_forces_of_forces_smul_blowup_mk_mem n huv⟩), Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      show Sym2.map (op_258_forces_of_forces_smul_blowup_emb γ n r)
          (Sym2.mk (op_258_forces_of_forces_smul_blowup_q γ n x) (op_258_forces_of_forces_smul_blowup_q γ n y)) = Sym2.mk x y
      rw [Sym2.map_mk,
        show op_258_forces_of_forces_smul_blowup_emb γ n r (op_258_forces_of_forces_smul_blowup_q γ n x) = x from by
          rw [← hbx]; exact op_258_forces_of_forces_smul_blowup_emb_bq γ n x,
        show op_258_forces_of_forces_smul_blowup_emb γ n r (op_258_forces_of_forces_smul_blowup_q γ n y) = y from by
          rw [← hby]; exact op_258_forces_of_forces_smul_blowup_emb_bq γ n y]
    have hagree := hc'agree _ hmem
    have hc0 := op_258_forces_of_forces_smul_blowup_c0_internal γ n c (hbx.trans hby.symm) huv hxy
    have hfin : c ⟨Sym2.mk (op_258_forces_of_forces_smul_blowup_q γ n x) (op_258_forces_of_forces_smul_blowup_q γ n y),
        op_258_forces_of_forces_smul_blowup_mk_mem n huv⟩ = i := by
      rw [← hc0, ← hagree]
      exact hmono'
    convert hfin
