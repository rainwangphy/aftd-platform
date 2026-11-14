import AFTD.Prelude
import AFTD.Kb.Tcs.TripartiteTuranHypergraph
import AFTD.Kb.Tcs.PairDigraphAdj

/-!
# tripartite_turan_pair_digraph_no_closed_walk

Topic: combinatorics   Node: dcf4394a972f

Provenance: helper lemma. arXiv:2611.16654 Lemma 3.3

For any family of pairwise disjoint finite sets V : ZMod 3 → Finset α and any integer ℓ with 3 ∤ ℓ, there is no closed walk W : ZMod ℓ → Finset α in the pair digraph of tripartite_turan_hypergraph V satisfying pair_digraph_adj (tripartite_turan_hypergraph V) (W i) (W (i + 1)) for all i in ZMod ℓ.
-/

noncomputable def pof {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α) (x : α) : ZMod 3 :=
  if h : ∃ i, x ∈ V i then h.choose else 0

lemma pof_eq {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α)
    (hdisj : ∀ i j : ZMod 3, i ≠ j → Disjoint (V i) (V j))
    {x : α} {i : ZMod 3} (hx : x ∈ V i) : pof V x = i := by
  have h : ∃ j, x ∈ V j := ⟨i, hx⟩
  have hspec : x ∈ V (Classical.choose h) := Classical.choose_spec h
  unfold pof
  rw [dif_pos h]
  by_contra hji
  exact (Finset.disjoint_left.mp (hdisj _ i hji)) hspec hx

lemma pof_mem {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α)
    {x : α} (h : ∃ i, x ∈ V i) : x ∈ V (pof V x) := by
  unfold pof
  rw [dif_pos h]
  exact Classical.choose_spec h

def prof (a b c j : ZMod 3) : ℕ := (if j = a then 1 else 0) + ((if j = b then 1 else 0) + (if j = c then 1 else 0))

abbrev ep (a b c : ZMod 3) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨ (a = b ∧ c = a + 1) ∨ (a = c ∧ b = a + 1) ∨ (b = c ∧ a = b + 1)

lemma inter_card_three {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α)
    (hdisj : ∀ i j : ZMod 3, i ≠ j → Disjoint (V i) (V j))
    {a b c : ZMod 3} {x y v : α}
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (hx : x ∈ V a) (hy : y ∈ V b) (hv : v ∈ V c) (j : ZMod 3) :
    (({x,y,v} : Finset α) ∩ V j).card = prof a b c j := by
  have hmemx : ∀ j, x ∈ V j ↔ j = a := by
    intro j; constructor
    · intro hj; by_contra h
      exact (Finset.disjoint_left.mp (hdisj j a h) hj) hx
    · intro h; rw [h]; exact hx
  have hmemy : ∀ j, y ∈ V j ↔ j = b := by
    intro j; constructor
    · intro hj; by_contra h
      exact (Finset.disjoint_left.mp (hdisj j b h) hj) hy
    · intro h; rw [h]; exact hy
  have hmemv : ∀ j, v ∈ V j ↔ j = c := by
    intro j; constructor
    · intro hj; by_contra h
      exact (Finset.disjoint_left.mp (hdisj j c h) hj) hv
    · intro h; rw [h]; exact hv
  show (({x,y,v} : Finset α) ∩ V j).card =
      (if j = a then 1 else 0) + ((if j = b then 1 else 0) + (if j = c then 1 else 0))
  rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_insert (by simp [hxy, hxv]), Finset.sum_insert (by simp [hyv]),
    Finset.sum_singleton]
  simp only [hmemx j, hmemy j, hmemv j]

lemma prof_edge_key : ∀ a b c : ZMod 3,
    ((∀ j, prof a b c j = 1) ∨ ∃ j, prof a b c j = 2 ∧ prof a b c (j+1) = 1) → ep a b c := by
  decide

lemma edge_profile {α : Type*} [DecidableEq α] (V : ZMod 3 → Finset α)
    (hdisj : ∀ i j : ZMod 3, i ≠ j → Disjoint (V i) (V j))
    {a b c : ZMod 3} {x y v : α}
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (hx : x ∈ V a) (hy : y ∈ V b) (hv : v ∈ V c)
    (he : (({x,y} : Finset α) ∪ {v}) ∈ tripartite_turan_hypergraph V) : ep a b c := by
  have hset : (({x,y} : Finset α) ∪ {v}) = ({x,y,v} : Finset α) := by
    ext w; simp
  rw [hset] at he
  have hcardj : ∀ j, (({x,y,v} : Finset α) ∩ V j).card = prof a b c j :=
    fun j => inter_card_three V hdisj hxy hxv hyv hx hy hv j
  have hcond := (Finset.mem_filter.mp he).2
  apply prof_edge_key
  rcases hcond with h | ⟨j, h2, h1⟩
  · left; intro j; rw [← hcardj j]; exact h j
  · right; exact ⟨j, by rw [← hcardj j]; exact h2, by rw [← hcardj (j+1)]; exact h1⟩

lemma same_key : ∀ a b a' b' : ZMod 3, a = b → ep a b a' → ep a b b' → (a' = b' ∧ a' + b' = a + b + 2) := by decide
lemma cross_key : ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' → ep a b a' → ep a b b' → (a' + b' = a + b + 1) := by decide

lemma zmod_shift_sum {n : ℕ} [NeZero n] (g : ZMod n → ZMod 3) :
    ∑ i : ZMod n, g (i+1) = ∑ i : ZMod n, g i := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a1 _ a2 _ h; exact add_right_cancel h
  · intro b _; exact ⟨b - 1, Finset.mem_univ _, by simp⟩
  · intro a _; rfl

lemma zmod_telescope {n : ℕ} [NeZero n] (g : ZMod n → ZMod 3) :
    ∑ i : ZMod n, (g (i+1) - g i) = 0 := by
  rw [Finset.sum_sub_distrib, zmod_shift_sum, sub_self]

lemma zmod3_nsmul_two_eq_zero (ℓ : ℕ) (h : ℓ • (2 : ZMod 3) = 0) : 3 ∣ ℓ := by
  have h2 : (2 : ZMod 3) * (ℓ : ZMod 3) = 0 := by
    rw [← h, nsmul_eq_mul]; ring
  have hunit : (2 : ZMod 3) ≠ 0 := by decide
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hunit
  · exact (CharP.cast_eq_zero_iff (ZMod 3) 3 ℓ).mp h3

lemma zmod3_nsmul_one_eq_zero (ℓ : ℕ) (h : ℓ • (1 : ZMod 3) = 0) : 3 ∣ ℓ := by
  rw [show ℓ • (1 : ZMod 3) = (ℓ : ZMod 3) by simp] at h
  exact (CharP.cast_eq_zero_iff (ZMod 3) 3 ℓ).mp h

/-- The pair digraph of the tripartite Turán construction contains no closed walk of length not divisible by 3. -/
theorem tripartite_turan_pair_digraph_no_closed_walk {α : Type*} [DecidableEq α]
    (V : ZMod 3 → Finset α) (hdisj : ∀ i j : ZMod 3, i ≠ j → Disjoint (V i) (V j))
    (ℓ : ℕ) [NeZero ℓ] (hℓ_not_dvd : ¬ 3 ∣ ℓ) :
    ¬ ∃ W : ZMod ℓ → Finset α, ∀ i : ZMod ℓ,
      pair_digraph_adj (tripartite_turan_hypergraph V) (W i) (W (i + 1)) := by
  rintro ⟨W, hW⟩
  have hcard1 : ∀ i, (W i).card = 2 := fun i => (hW i).1
  have hadj : ∀ i, ∀ v ∈ W (i+1), W i ∪ {v} ∈ tripartite_turan_hypergraph V := fun i => (hW i).2.2
  have hWne : ∀ i, (W i).Nonempty := fun i =>
    Finset.card_pos.mp (by rw [hcard1 i]; norm_num)
  have hWsub : ∀ i, W i ⊆ Finset.univ.biUnion V := by
    intro i z hz
    obtain ⟨w, hw⟩ := hWne (i+1)
    have hmem := hadj i w hw
    have hsub := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hmem).1).1
    exact hsub (Finset.mem_union_left _ hz)
  have h2 : ∀ i, ∃ x y : α, x ≠ y ∧ W i = {x,y} := fun i => Finset.card_eq_two.mp (hcard1 i)
  let xf : ZMod ℓ → α := fun i => (h2 i).choose
  let yf : ZMod ℓ → α := fun i => (h2 i).choose_spec.choose
  have hxfyf : ∀ i, xf i ≠ yf i ∧ W i = {xf i, yf i} := fun i => (h2 i).choose_spec.choose_spec
  let a : ZMod ℓ → ZMod 3 := fun i => pof V (xf i)
  let b : ZMod ℓ → ZMod 3 := fun i => pof V (yf i)
  have hxpart : ∀ i, ∃ p, xf i ∈ V p := fun i => by
    have hmem : xf i ∈ W i := by rw [(hxfyf i).2]; exact Finset.mem_insert_self _ _
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp (hWsub i hmem)
    exact ⟨p, hp⟩
  have hypart : ∀ i, ∃ p, yf i ∈ V p := fun i => by
    have hmem : yf i ∈ W i := by rw [(hxfyf i).2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp (hWsub i hmem)
    exact ⟨p, hp⟩
  have hax : ∀ i, xf i ∈ V (a i) := fun i => pof_mem V (hxpart i)
  have hbx : ∀ i, yf i ∈ V (b i) := fun i => pof_mem V (hypart i)
  have hprofA : ∀ i, ep (a i) (b i) (a (i+1)) := by
    intro i
    have hxy : xf i ≠ yf i := (hxfyf i).1
    have he : W i ∪ {xf (i+1)} ∈ tripartite_turan_hypergraph V := by
      apply hadj i; rw [(hxfyf (i+1)).2]; exact Finset.mem_insert_self _ _
    rw [(hxfyf i).2] at he
    have hnotin : xf (i+1) ∉ ({xf i, yf i} : Finset α) := by
      intro hin
      have hun : (({xf i, yf i} : Finset α) ∪ {xf (i+1)}) = {xf i, yf i} := by
        rw [Finset.union_eq_left]
        rw [Finset.singleton_subset_iff]; exact hin
      rw [hun] at he
      have hc3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      rw [Finset.card_pair hxy] at hc3
      exact absurd hc3 (by norm_num)
    have hne1 : xf (i+1) ≠ xf i := by intro h; apply hnotin; simp [h]
    have hne2 : xf (i+1) ≠ yf i := by intro h; apply hnotin; simp [h]
    exact edge_profile V hdisj (a := a i) (b := b i) (c := a (i+1))
      hxy (Ne.symm hne1) (Ne.symm hne2) (hax i) (hbx i) (hax (i+1)) he
  have hprofB : ∀ i, ep (a i) (b i) (b (i+1)) := by
    intro i
    have hxy : xf i ≠ yf i := (hxfyf i).1
    have he : W i ∪ {yf (i+1)} ∈ tripartite_turan_hypergraph V := by
      apply hadj i; rw [(hxfyf (i+1)).2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [(hxfyf i).2] at he
    have hnotin : yf (i+1) ∉ ({xf i, yf i} : Finset α) := by
      intro hin
      have hun : (({xf i, yf i} : Finset α) ∪ {yf (i+1)}) = {xf i, yf i} := by
        rw [Finset.union_eq_left]
        rw [Finset.singleton_subset_iff]; exact hin
      rw [hun] at he
      have hc3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      rw [Finset.card_pair hxy] at hc3
      exact absurd hc3 (by norm_num)
    have hne1 : yf (i+1) ≠ xf i := by intro h; apply hnotin; simp [h]
    have hne2 : yf (i+1) ≠ yf i := by intro h; apply hnotin; simp [h]
    exact edge_profile V hdisj (a := a i) (b := b i) (c := b (i+1))
      hxy (Ne.symm hne1) (Ne.symm hne2) (hax i) (hbx i) (hbx (i+1)) he
  have hsame : ∀ i, a i = b i → a (i+1) = b (i+1) ∧ (a (i+1) + b (i+1)) = (a i + b i) + 2 :=
    fun i h => same_key (a i) (b i) (a (i+1)) (b (i+1)) h (hprofA i) (hprofB i)
  have hcross : ∀ i, a i ≠ b i → a (i+1) ≠ b (i+1) → (a (i+1) + b (i+1)) = (a i + b i) + 1 :=
    fun i h h' => cross_key (a i) (b i) (a (i+1)) (b (i+1)) h h' (hprofA i) (hprofB i)
  by_cases hex : ∃ i, a i = b i
  · obtain ⟨i0, hi0⟩ := hex
    have hforward : ∀ i, a i = b i → a (i+1) = b (i+1) := fun i h => (hsame i h).1
    have hall : ∀ j, a j = b j := by
      have hkey : ∀ k : ℕ, a (i0 + (k : ZMod ℓ)) = b (i0 + (k : ZMod ℓ)) := by
        intro k
        induction k with
        | zero => simpa using hi0
        | succ k ih =>
            have hh := hforward (i0 + (k : ZMod ℓ)) ih
            simpa [Nat.cast_succ, add_assoc] using hh
      intro j
      have hrepr : j = i0 + ((j - i0).val : ZMod ℓ) := by
        rw [ZMod.natCast_zmod_val]; abel
      rw [hrepr]; exact hkey _
    have hstep : ∀ i, (a (i+1) + b (i+1)) - (a i + b i) = (2 : ZMod 3) := by
      intro i
      have hh := (hsame i (hall i)).2
      rw [hh]; abel
    have hsum : ∑ i : ZMod ℓ, ((a (i+1) + b (i+1)) - (a i + b i)) = ∑ i : ZMod ℓ, (2 : ZMod 3) :=
      Finset.sum_congr rfl (fun i _ => hstep i)
    have htz := zmod_telescope (fun i => a i + b i)
    rw [hsum] at htz
    have hconst : ∑ i : ZMod ℓ, (2 : ZMod 3) = ℓ • (2 : ZMod 3) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [hconst] at htz
    exact hℓ_not_dvd (zmod3_nsmul_two_eq_zero ℓ htz)
  · push_neg at hex
    have hstep : ∀ i, (a (i+1) + b (i+1)) - (a i + b i) = (1 : ZMod 3) := by
      intro i
      have hh := hcross i (hex i) (hex (i+1))
      rw [hh]; abel
    have hsum : ∑ i : ZMod ℓ, ((a (i+1) + b (i+1)) - (a i + b i)) = ∑ i : ZMod ℓ, (1 : ZMod 3) :=
      Finset.sum_congr rfl (fun i _ => hstep i)
    have htz := zmod_telescope (fun i => a i + b i)
    rw [hsum] at htz
    have hconst : ∑ i : ZMod ℓ, (1 : ZMod 3) = ℓ • (1 : ZMod 3) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [hconst] at htz
    exact hℓ_not_dvd (zmod3_nsmul_one_eq_zero ℓ htz)
