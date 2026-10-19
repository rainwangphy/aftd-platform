import AFTD.Prelude
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.HandshakeUpdateContam

/-!
# has_clean_handshake_seq_succ

Topic: combinatorics   Node: d898369b149f

Provenance: helper lemma. step towards glove_number_complete_graph_open_problem

If a graph $G$ admits a clean handshake sequence with $k$ gloves, then it admits one with $k+1$ gloves: an extra glove can be left unused.
-/

def has_clean_handshake_seq_succ_sideMap {Γ Γ' : Type*} (f : Γ → Γ') :
    Γ × Bool → Γ' × Bool := fun s => (f s.1, s.2)

def has_clean_handshake_seq_succ_mapGlove {V Γ Γ' : Type*} (f : Γ → Γ') :
    Handshake V Γ → Handshake V Γ'
  | Handshake.single x a y => Handshake.single x (has_clean_handshake_seq_succ_sideMap f a) y
  | Handshake.double x a b y =>
      Handshake.double x (has_clean_handshake_seq_succ_sideMap f a)
        (has_clean_handshake_seq_succ_sideMap f b) y

noncomputable def has_clean_handshake_seq_succ_pushContam {V Γ Γ' : Type*} (f : Γ → Γ')
    (t : Γ × Bool → Set V) : Γ' × Bool → Set V := by
  classical
  exact fun s' => if h : ∃ a, has_clean_handshake_seq_succ_sideMap f a = s' then t h.choose else ∅

theorem has_clean_handshake_seq_succ_pushContam_apply {V Γ Γ' : Type*} (f : Γ → Γ')
    (hf : Function.Injective f) (t : Γ × Bool → Set V) (a : Γ × Bool) :
    has_clean_handshake_seq_succ_pushContam f t (has_clean_handshake_seq_succ_sideMap f a) = t a := by
  classical
  unfold has_clean_handshake_seq_succ_pushContam
  split_ifs with h
  · congr 1
    have hspec : (f h.choose.1, h.choose.2) = (f a.1, a.2) := by
      simpa only [has_clean_handshake_seq_succ_sideMap] using Exists.choose_spec h
    exact Prod.ext (hf (Prod.mk.inj hspec).1) (Prod.mk.inj hspec).2
  · exact absurd ⟨a, rfl⟩ h

theorem has_clean_handshake_seq_succ_pushContam_of_not_mem {V Γ Γ' : Type*} (f : Γ → Γ')
    (t : Γ × Bool → Set V) (s' : Γ' × Bool)
    (hs' : ¬ ∃ a, has_clean_handshake_seq_succ_sideMap f a = s') :
    has_clean_handshake_seq_succ_pushContam f t s' = ∅ := by
  classical
  unfold has_clean_handshake_seq_succ_pushContam
  exact dif_neg hs'

theorem has_clean_handshake_seq_succ_pushContam_empty {V Γ Γ' : Type*} (f : Γ → Γ') :
    has_clean_handshake_seq_succ_pushContam (V := V) f (fun _ => ∅) = fun _ => ∅ := by
  classical
  funext s'
  unfold has_clean_handshake_seq_succ_pushContam
  by_cases h : ∃ a, has_clean_handshake_seq_succ_sideMap f a = s'
  · rw [dif_pos h]
  · rw [dif_neg h]

theorem has_clean_handshake_seq_succ_sideMap_opp {Γ Γ' : Type*} (f : Γ → Γ') (a : Γ × Bool) :
    has_clean_handshake_seq_succ_sideMap f (opp_glove_side a)
      = opp_glove_side (has_clean_handshake_seq_succ_sideMap f a) := rfl

theorem has_clean_handshake_seq_succ_sideMap_inj {Γ Γ' : Type*} (f : Γ → Γ')
    (hf : Function.Injective f) (x y : Γ × Bool) :
    has_clean_handshake_seq_succ_sideMap f x = has_clean_handshake_seq_succ_sideMap f y ↔ x = y := by
  constructor
  · intro h
    simp only [has_clean_handshake_seq_succ_sideMap, Prod.mk.injEq] at h
    exact Prod.ext (hf h.1) h.2
  · intro h; rw [h]

theorem has_clean_handshake_seq_succ_edge_mapGlove {V Γ Γ' : Type*} (f : Γ → Γ')
    (h : Handshake V Γ) :
    handshake_edge (has_clean_handshake_seq_succ_mapGlove f h) = handshake_edge h := by
  cases h <;> rfl

theorem has_clean_handshake_seq_succ_clean_mapGlove {V Γ Γ' : Type*} (f : Γ → Γ')
    (hf : Function.Injective f) (h : Handshake V Γ) (t : Γ × Bool → Set V) :
    handshake_is_clean h t →
      handshake_is_clean (has_clean_handshake_seq_succ_mapGlove f h)
        (has_clean_handshake_seq_succ_pushContam f t) := by
  intro hc
  cases h with
  | single x a y =>
    simp only [has_clean_handshake_seq_succ_mapGlove, handshake_is_clean] at hc ⊢
    rw [← has_clean_handshake_seq_succ_sideMap_opp,
      has_clean_handshake_seq_succ_pushContam_apply f hf,
      has_clean_handshake_seq_succ_pushContam_apply f hf]
    exact hc
  | double x a b y =>
    simp only [has_clean_handshake_seq_succ_mapGlove, handshake_is_clean] at hc ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro he; exact hc.1 (hf he)
    · rw [has_clean_handshake_seq_succ_pushContam_apply f hf]; exact hc.2.1
    · rw [has_clean_handshake_seq_succ_pushContam_apply f hf]; exact hc.2.2

theorem has_clean_handshake_seq_succ_pushContam_update {V Γ Γ' : Type*}
    [DecidableEq Γ] [DecidableEq Γ'] (f : Γ → Γ') (hf : Function.Injective f)
    (h : Handshake V Γ) (t : Γ × Bool → Set V) :
    has_clean_handshake_seq_succ_pushContam f (handshake_update_contam h t)
      = handshake_update_contam (has_clean_handshake_seq_succ_mapGlove f h)
          (has_clean_handshake_seq_succ_pushContam f t) := by
  classical
  cases h with
  | single x a y =>
    funext s'
    by_cases hs' : ∃ a, has_clean_handshake_seq_succ_sideMap f a = s'
    · obtain ⟨a', ha'⟩ := hs'
      rw [← ha']
      simp only [has_clean_handshake_seq_succ_mapGlove, handshake_update_contam,
        ← has_clean_handshake_seq_succ_sideMap_opp,
        has_clean_handshake_seq_succ_pushContam_apply f hf,
        has_clean_handshake_seq_succ_sideMap_inj f hf]
    · rw [has_clean_handshake_seq_succ_pushContam_of_not_mem f _ s' hs']
      have h1 : s' ≠ has_clean_handshake_seq_succ_sideMap f a := fun he => hs' ⟨a, he.symm⟩
      have h2 : s' ≠ opp_glove_side (has_clean_handshake_seq_succ_sideMap f a) := by
        rw [← has_clean_handshake_seq_succ_sideMap_opp]
        exact fun he => hs' ⟨opp_glove_side a, he.symm⟩
      simp only [has_clean_handshake_seq_succ_mapGlove, handshake_update_contam, h1, h2,
        has_clean_handshake_seq_succ_pushContam_of_not_mem f t s' hs']
      simp
  | double x a b y =>
    funext s'
    by_cases hs' : ∃ a, has_clean_handshake_seq_succ_sideMap f a = s'
    · obtain ⟨a', ha'⟩ := hs'
      rw [← ha']
      simp only [has_clean_handshake_seq_succ_mapGlove, handshake_update_contam,
        ← has_clean_handshake_seq_succ_sideMap_opp,
        has_clean_handshake_seq_succ_pushContam_apply f hf,
        has_clean_handshake_seq_succ_sideMap_inj f hf]
    · rw [has_clean_handshake_seq_succ_pushContam_of_not_mem f _ s' hs']
      have h1 : s' ≠ has_clean_handshake_seq_succ_sideMap f a := fun he => hs' ⟨a, he.symm⟩
      have h2 : s' ≠ has_clean_handshake_seq_succ_sideMap f b := fun he => hs' ⟨b, he.symm⟩
      have h3 : s' ≠ opp_glove_side (has_clean_handshake_seq_succ_sideMap f a) := by
        rw [← has_clean_handshake_seq_succ_sideMap_opp]
        exact fun he => hs' ⟨opp_glove_side a, he.symm⟩
      have h4 : s' ≠ opp_glove_side (has_clean_handshake_seq_succ_sideMap f b) := by
        rw [← has_clean_handshake_seq_succ_sideMap_opp]
        exact fun he => hs' ⟨opp_glove_side b, he.symm⟩
      simp only [has_clean_handshake_seq_succ_mapGlove, handshake_update_contam, h1, h2, h3, h4,
        has_clean_handshake_seq_succ_pushContam_of_not_mem f t s' hs']
      simp

theorem has_clean_handshake_seq_succ_clean_seq_map {V Γ Γ' : Type*}
    [DecidableEq Γ] [DecidableEq Γ'] (f : Γ → Γ') (hf : Function.Injective f) :
    ∀ (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V),
      CleanHandshakeSeq seq t →
      CleanHandshakeSeq (seq.map (has_clean_handshake_seq_succ_mapGlove f))
        (has_clean_handshake_seq_succ_pushContam f t) := by
  intro seq t hseq
  induction hseq with
  | nil t => exact CleanHandshakeSeq.nil _
  | cons h seq t hclean htail ih =>
    rw [List.map_cons]
    refine CleanHandshakeSeq.cons (has_clean_handshake_seq_succ_mapGlove f h)
      (seq.map (has_clean_handshake_seq_succ_mapGlove f))
      (has_clean_handshake_seq_succ_pushContam f t) ?_ ?_
    · exact has_clean_handshake_seq_succ_clean_mapGlove f hf h t hclean
    · rw [← has_clean_handshake_seq_succ_pushContam_update f hf h t]
      exact ih

/-- An unused glove can always be added: `k` gloves suffice implies `k+1` gloves suffice. -/
theorem has_clean_handshake_seq_succ {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    has_clean_handshake_seq G k → has_clean_handshake_seq G (k + 1) := by
  rintro ⟨seq, hclean, hcover⟩
  refine ⟨seq.map (has_clean_handshake_seq_succ_mapGlove (Fin.castSucc (n := k))), ?_, ?_⟩
  · have h := has_clean_handshake_seq_succ_clean_seq_map (f := Fin.castSucc (n := k))
        (Fin.castSucc_injective k) seq (fun _ => ∅) hclean
    rw [has_clean_handshake_seq_succ_pushContam_empty] at h
    exact h
  · intro e he
    obtain ⟨h, hh, hedge⟩ := hcover e he
    refine ⟨has_clean_handshake_seq_succ_mapGlove (Fin.castSucc (n := k)) h, ?_, ?_⟩
    · simp only [List.mem_map]; exact ⟨h, hh, rfl⟩
    · rw [has_clean_handshake_seq_succ_edge_mapGlove]; exact hedge
