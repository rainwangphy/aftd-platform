import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeUpdateContam
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.OppGloveSide

/-!
# glove_number_complete_graph_upper_bound

Topic: combinatorics   Node: 913eb721bcfb

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:653

For all integers $n \ge 2$, the glove number of the complete graph $K_n$ is at most $n - 1$.
-/

def glove_number_complete_graph_upper_bound_is_phase1_handshake {m : ℕ}
    (h : Handshake (Fin (m + 1)) (Fin m)) : Prop :=
  ∃ (i j : Fin m), i ≠ j ∧ h = Handshake.double i.castSucc (i, true) (j, true) j.castSucc

def glove_number_complete_graph_upper_bound_is_phase2_handshake {m : ℕ}
    (h : Handshake (Fin (m + 1)) (Fin m)) : Prop :=
  ∃ (i : Fin m), h = Handshake.single (Fin.last m) (i, false) i.castSucc

def glove_number_complete_graph_upper_bound_inv1 {m : ℕ}
    (t : Fin m × Bool → Set (Fin (m + 1))) : Prop :=
  (∀ k, t (k, false) = ∅) ∧ (∀ k, t (k, true) ⊆ {k.castSucc})

def glove_number_complete_graph_upper_bound_inv2 {m : ℕ}
    (t : Fin m × Bool → Set (Fin (m + 1))) : Prop :=
  ∀ k, t (k, false) ⊆ {Fin.last m} ∧ t (k, true) ⊆ {k.castSucc}

lemma glove_number_complete_graph_upper_bound_inv1_imp_inv2 {m : ℕ}
    {t : Fin m × Bool → Set (Fin (m + 1))}
    (ht : glove_number_complete_graph_upper_bound_inv1 t) :
    glove_number_complete_graph_upper_bound_inv2 t := by
  intro k
  constructor
  · rw [ht.1 k]
    exact Set.empty_subset _
  · exact ht.2 k

lemma glove_number_complete_graph_upper_bound_phase1_step_clean {m : ℕ}
    {h : Handshake (Fin (m + 1)) (Fin m)} {t : Fin m × Bool → Set (Fin (m + 1))}
    (hh : glove_number_complete_graph_upper_bound_is_phase1_handshake h)
    (ht : glove_number_complete_graph_upper_bound_inv1 t) :
    handshake_is_clean h t := by
  rcases hh with ⟨i, j, hij, rfl⟩
  dsimp [handshake_is_clean]
  exact ⟨hij, ht.2 i, ht.2 j⟩

lemma glove_number_complete_graph_upper_bound_phase1_step_inv {m : ℕ}
    {h : Handshake (Fin (m + 1)) (Fin m)} {t : Fin m × Bool → Set (Fin (m + 1))}
    (hh : glove_number_complete_graph_upper_bound_is_phase1_handshake h)
    (ht : glove_number_complete_graph_upper_bound_inv1 t) :
    glove_number_complete_graph_upper_bound_inv1 (handshake_update_contam h t) := by
  rcases hh with ⟨i, j, hij, rfl⟩
  constructor
  · intro k
    change (if (k, false) = (i, true) then t (i, true) ∪ {i.castSucc}
            else if (k, false) = (j, true) then t (j, true) ∪ {j.castSucc}
            else if (k, false) = (i, false) ∨ (k, false) = (j, false) then t (i, false) ∪ t (j, false)
            else t (k, false)) = ∅
    have h1 : ¬ (k, false) = (i, true) := by intro h; cases h
    have h2 : ¬ (k, false) = (j, true) := by intro h; cases h
    rw [if_neg h1, if_neg h2]
    split_ifs with h3
    · rw [ht.1 i, ht.1 j, Set.union_empty]
    · exact ht.1 k
  · intro k
    change (if (k, true) = (i, true) then t (i, true) ∪ {i.castSucc}
            else if (k, true) = (j, true) then t (j, true) ∪ {j.castSucc}
            else if (k, true) = (i, false) ∨ (k, true) = (j, false) then t (i, false) ∪ t (j, false)
            else t (k, true)) ⊆ {k.castSucc}
    split_ifs with h1 h2 h3
    · injection h1 with hi
      subst hi
      exact Set.union_subset (ht.2 k) (Set.Subset.refl _)
    · injection h2 with hj
      subst hj
      exact Set.union_subset (ht.2 k) (Set.Subset.refl _)
    · rcases h3 with h3 | h3 <;> cases h3
    · exact ht.2 k

lemma glove_number_complete_graph_upper_bound_phase2_step_clean {m : ℕ}
    {h : Handshake (Fin (m + 1)) (Fin m)} {t : Fin m × Bool → Set (Fin (m + 1))}
    (hh : glove_number_complete_graph_upper_bound_is_phase2_handshake h)
    (ht : glove_number_complete_graph_upper_bound_inv2 t) :
    handshake_is_clean h t := by
  rcases hh with ⟨i, rfl⟩
  dsimp [handshake_is_clean, opp_glove_side]
  exact ⟨(ht i).1, (ht i).2⟩

lemma glove_number_complete_graph_upper_bound_phase2_step_inv {m : ℕ}
    {h : Handshake (Fin (m + 1)) (Fin m)} {t : Fin m × Bool → Set (Fin (m + 1))}
    (hh : glove_number_complete_graph_upper_bound_is_phase2_handshake h)
    (ht : glove_number_complete_graph_upper_bound_inv2 t) :
    glove_number_complete_graph_upper_bound_inv2 (handshake_update_contam h t) := by
  rcases hh with ⟨i, rfl⟩
  intro k
  constructor
  · change (if (k, false) = (i, false) then t (i, false) ∪ {Fin.last m}
            else if (k, false) = (i, true) then t (i, true) ∪ {i.castSucc}
            else t (k, false)) ⊆ {Fin.last m}
    split_ifs with h1 h2
    · injection h1 with hi
      subst hi
      exact Set.union_subset (ht k).1 (Set.Subset.refl _)
    · cases h2
    · exact (ht k).1
  · change (if (k, true) = (i, false) then t (i, false) ∪ {Fin.last m}
            else if (k, true) = (i, true) then t (i, true) ∪ {i.castSucc}
            else t (k, true)) ⊆ {k.castSucc}
    split_ifs with h1 h2
    · cases h1
    · injection h2 with hi
      subst hi
      exact Set.union_subset (ht k).2 (Set.Subset.refl _)
    · exact (ht k).2

lemma glove_number_complete_graph_upper_bound_clean_seq_phase2 {m : ℕ}
    (seq : List (Handshake (Fin (m + 1)) (Fin m)))
    (hseq : ∀ h ∈ seq, glove_number_complete_graph_upper_bound_is_phase2_handshake h)
    {t} (ht : glove_number_complete_graph_upper_bound_inv2 t) :
    CleanHandshakeSeq seq t := by
  induction seq generalizing t with
  | nil => exact CleanHandshakeSeq.nil t
  | cons h rest ih =>
    have hh : glove_number_complete_graph_upper_bound_is_phase2_handshake h := hseq h List.mem_cons_self
    have hrest : ∀ h' ∈ rest, glove_number_complete_graph_upper_bound_is_phase2_handshake h' :=
      fun h' mh' => hseq h' (List.mem_cons_of_mem _ mh')
    have hc := glove_number_complete_graph_upper_bound_phase2_step_clean hh ht
    have hi := glove_number_complete_graph_upper_bound_phase2_step_inv hh ht
    exact CleanHandshakeSeq.cons h rest t hc (ih hrest hi)

lemma glove_number_complete_graph_upper_bound_clean_seq_phase1_then_phase2 {m : ℕ}
    (seq1 seq2 : List (Handshake (Fin (m + 1)) (Fin m)))
    (hseq1 : ∀ h ∈ seq1, glove_number_complete_graph_upper_bound_is_phase1_handshake h)
    (hseq2 : ∀ h ∈ seq2, glove_number_complete_graph_upper_bound_is_phase2_handshake h)
    {t} (ht : glove_number_complete_graph_upper_bound_inv1 t) :
    CleanHandshakeSeq (seq1 ++ seq2) t := by
  induction seq1 generalizing t with
  | nil =>
    exact glove_number_complete_graph_upper_bound_clean_seq_phase2 seq2 hseq2
      (glove_number_complete_graph_upper_bound_inv1_imp_inv2 ht)
  | cons h rest ih =>
    have hh : glove_number_complete_graph_upper_bound_is_phase1_handshake h := hseq1 h List.mem_cons_self
    have hrest : ∀ h' ∈ rest, glove_number_complete_graph_upper_bound_is_phase1_handshake h' :=
      fun h' mh' => hseq1 h' (List.mem_cons_of_mem _ mh')
    have hc := glove_number_complete_graph_upper_bound_phase1_step_clean hh ht
    have hi := glove_number_complete_graph_upper_bound_phase1_step_inv hh ht
    exact CleanHandshakeSeq.cons h (rest ++ seq2) t hc (ih hrest hi)

def glove_number_complete_graph_upper_bound_phase1 (m : ℕ) :
    List (Handshake (Fin (m + 1)) (Fin m)) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange m).filterMap fun j =>
      if _h : i ≠ j then
        some (Handshake.double i.castSucc (i, true) (j, true) j.castSucc)
      else none

def glove_number_complete_graph_upper_bound_phase2 (m : ℕ) :
    List (Handshake (Fin (m + 1)) (Fin m)) :=
  (List.finRange m).map fun i =>
    Handshake.single (Fin.last m) (i, false) i.castSucc

lemma glove_number_complete_graph_upper_bound_phase1_all_is_phase1 (m : ℕ) :
    ∀ h ∈ glove_number_complete_graph_upper_bound_phase1 m,
      glove_number_complete_graph_upper_bound_is_phase1_handshake h := by
  intro h hh
  dsimp [glove_number_complete_graph_upper_bound_phase1] at hh
  rw [List.mem_flatMap] at hh
  rcases hh with ⟨i, _, hi⟩
  rw [List.mem_filterMap] at hi
  rcases hi with ⟨j, _, hj⟩
  split_ifs at hj with hij
  · injection hj with heq
    subst heq
    exact ⟨i, j, hij, rfl⟩

lemma glove_number_complete_graph_upper_bound_phase2_all_is_phase2 (m : ℕ) :
    ∀ h ∈ glove_number_complete_graph_upper_bound_phase2 m,
      glove_number_complete_graph_upper_bound_is_phase2_handshake h := by
  intro h hh
  dsimp [glove_number_complete_graph_upper_bound_phase2] at hh
  rw [List.mem_map] at hh
  rcases hh with ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

lemma glove_number_complete_graph_upper_bound_mem_phase1 {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Handshake.double i.castSucc (i, true) (j, true) j.castSucc ∈
      glove_number_complete_graph_upper_bound_phase1 m := by
  dsimp [glove_number_complete_graph_upper_bound_phase1]
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_finRange i, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨j, List.mem_finRange j, ?_⟩
  simp [hij]

lemma glove_number_complete_graph_upper_bound_mem_phase2 {m : ℕ} (i : Fin m) :
    Handshake.single (Fin.last m) (i, false) i.castSucc ∈
      glove_number_complete_graph_upper_bound_phase2 m := by
  dsimp [glove_number_complete_graph_upper_bound_phase2]
  rw [List.mem_map]
  exact ⟨i, List.mem_finRange i, rfl⟩

lemma glove_number_complete_graph_upper_bound_edges_covered (m : ℕ) (e : Sym2 (Fin (m + 1)))
    (he : e ∈ (SimpleGraph.completeGraph (Fin (m + 1))).edgeSet) :
    ∃ h ∈ glove_number_complete_graph_upper_bound_phase1 m ++
      glove_number_complete_graph_upper_bound_phase2 m, handshake_edge h = e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : u ≠ v := he
    rcases Fin.eq_castSucc_or_eq_last u with (⟨i, rfl⟩ | rfl)
    · rcases Fin.eq_castSucc_or_eq_last v with (⟨j, rfl⟩ | rfl)
      · have hij : i ≠ j := by
          intro h; apply huv; subst h; rfl
        refine ⟨Handshake.double i.castSucc (i, true) (j, true) j.castSucc, ?_, rfl⟩
        exact List.mem_append_left _ (glove_number_complete_graph_upper_bound_mem_phase1 hij)
      · refine ⟨Handshake.single (Fin.last m) (i, false) i.castSucc, ?_, ?_⟩
        · exact List.mem_append_right _ (glove_number_complete_graph_upper_bound_mem_phase2 i)
        · dsimp [handshake_edge]; rw [Sym2.eq_swap]
    · rcases Fin.eq_castSucc_or_eq_last v with (⟨j, rfl⟩ | rfl)
      · refine ⟨Handshake.single (Fin.last m) (j, false) j.castSucc, ?_, rfl⟩
        exact List.mem_append_right _ (glove_number_complete_graph_upper_bound_mem_phase2 j)
      · contradiction

lemma glove_number_complete_graph_upper_bound_has_clean_seq (m : ℕ) :
    has_clean_handshake_seq (SimpleGraph.completeGraph (Fin (m + 1))) m := by
  use glove_number_complete_graph_upper_bound_phase1 m ++
      glove_number_complete_graph_upper_bound_phase2 m
  constructor
  · have hinit : glove_number_complete_graph_upper_bound_inv1
        (fun (_ : Fin m × Bool) => (∅ : Set (Fin (m + 1)))) := by
      constructor
      · intro k; rfl
      · intro k; exact Set.empty_subset _
    exact glove_number_complete_graph_upper_bound_clean_seq_phase1_then_phase2
      (glove_number_complete_graph_upper_bound_phase1 m)
      (glove_number_complete_graph_upper_bound_phase2 m)
      (glove_number_complete_graph_upper_bound_phase1_all_is_phase1 m)
      (glove_number_complete_graph_upper_bound_phase2_all_is_phase2 m)
      hinit
  · intro e he
    exact glove_number_complete_graph_upper_bound_edges_covered m e he

/-- Upper bound: gl(K_n) <= n - 1 for all n >= 2. -/
theorem glove_number_complete_graph_upper_bound (n : ℕ) (hn : 2 ≤ n) : glove_number (SimpleGraph.completeGraph (Fin n)) ≤ n - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  subst hm
  simp only [Nat.add_sub_cancel]
  have hseq := glove_number_complete_graph_upper_bound_has_clean_seq m
  exact Nat.sInf_le hseq
