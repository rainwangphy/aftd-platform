import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.GloveNumberCompleteGraphNoZeroGloves
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.HandshakeIsClean
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.HandshakeUpdateContam

/-!
# glove_number_complete_graph_pos

Topic: combinatorics   Node: c3d07ba2d742

Provenance: helper lemma. arXiv:2610.17602 Section 2 (Clean handshake sequences)

For every integer $n \ge 2$, the glove number of the complete graph $K_n$ is at least 1.
-/

/-- A double handshake in which the first vertex wears the `false` side of glove `2 * φ p` and the
second vertex wears the `false` side of glove `2 * φ p + 1`. -/
def glove_number_complete_graph_pos_hs {ι V : Type*} (K : ℕ) (φ : ι → ℕ)
    (hb : ∀ p, 2 * φ p + 1 < K) (e : ι → V × V) (p : ι) : Handshake V (Fin K) :=
  Handshake.double (e p).1 (⟨2 * φ p, by have := hb p; omega⟩, false)
    (⟨2 * φ p + 1, by have := hb p; omega⟩, false) (e p).2

/-- The edge covered by such a double handshake. -/
lemma glove_number_complete_graph_pos_hs_edge {ι V : Type*} (K : ℕ) (φ : ι → ℕ)
    (hb : ∀ p, 2 * φ p + 1 < K) (e : ι → V × V) (p : ι) :
    handshake_edge (glove_number_complete_graph_pos_hs K φ hb e p) = Sym2.mk (e p).1 (e p).2 :=
  rfl

/-- The contamination update of such a handshake leaves untouched every glove side whose glove
index differs from `2 * φ p` and `2 * φ p + 1`. -/
lemma glove_number_complete_graph_pos_hs_update {ι V : Type*} (K : ℕ) (φ : ι → ℕ)
    (hb : ∀ p, 2 * φ p + 1 < K) (e : ι → V × V) (p : ι)
    (t : Fin K × Bool → Set V) (s : Fin K × Bool)
    (h1 : s.1.val ≠ 2 * φ p) (h2 : s.1.val ≠ 2 * φ p + 1) :
    handshake_update_contam (glove_number_complete_graph_pos_hs K φ hb e p) t s = t s := by
  simp only [glove_number_complete_graph_pos_hs, handshake_update_contam]
  split_ifs with h h' h''
  · exact absurd (by rw [h]) h1
  · exact absurd (by rw [h']) h2
  · rcases h'' with h'' | h''
    · exact absurd (by rw [h'']; rfl) h1
    · exact absurd (by rw [h'']; rfl) h2
  · rfl

/-- If the glove index map `φ` is injective and every glove side whose index is not among the
already processed indices `P` is uncontaminated, then the sequence of fresh double handshakes
along a duplicate-free list `L` disjoint from `P` is clean. -/
lemma glove_number_complete_graph_pos_clean {ι V : Type*} (K : ℕ) (φ : ι → ℕ)
    (hφ : Function.Injective φ) (hb : ∀ p, 2 * φ p + 1 < K) (e : ι → V × V)
    (L P : List ι) (t : Fin K × Bool → Set V)
    (hL : L.Nodup) (hdisj : ∀ p ∈ L, p ∉ P)
    (hinv : ∀ s : Fin K × Bool, (∀ q ∈ P, s.1.val ≠ 2 * φ q ∧ s.1.val ≠ 2 * φ q + 1) → t s = ∅) :
    CleanHandshakeSeq (L.map (glove_number_complete_graph_pos_hs K φ hb e)) t := by
  induction L generalizing P t with
  | nil => exact CleanHandshakeSeq.nil t
  | cons p L ih =>
    obtain ⟨hpL, hL'⟩ := List.nodup_cons.mp hL
    have hpP : p ∉ P := hdisj p (List.mem_cons_self ..)
    have hkey : ∀ q ∈ P, 2 * φ p ≠ 2 * φ q ∧ 2 * φ p ≠ 2 * φ q + 1 := by
      intro q hq
      refine ⟨fun h => hpP ?_, fun h => by omega⟩
      have hpq : φ p = φ q := by omega
      rw [hφ hpq]; exact hq
    have hempty1 : t ((⟨2 * φ p, by have := hb p; omega⟩ : Fin K), false) = ∅ :=
      hinv _ hkey
    have hempty2 : t ((⟨2 * φ p + 1, by have := hb p; omega⟩ : Fin K), false) = ∅ := by
      refine hinv _ ?_
      intro q hq
      have hk := hkey q hq
      constructor
      · show 2 * φ p + 1 ≠ 2 * φ q
        omega
      · show 2 * φ p + 1 ≠ 2 * φ q + 1
        omega
    have hclean : handshake_is_clean (glove_number_complete_graph_pos_hs K φ hb e p) t := by
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have hv : (2 : ℕ) * φ p = 2 * φ p + 1 := congrArg Fin.val h
        omega
      · rw [hempty1]; exact Set.empty_subset _
      · rw [hempty2]; exact Set.empty_subset _
    have hinv' : ∀ s : Fin K × Bool, (∀ q ∈ p :: P, s.1.val ≠ 2 * φ q ∧ s.1.val ≠ 2 * φ q + 1) →
        handshake_update_contam (glove_number_complete_graph_pos_hs K φ hb e p) t s = ∅ := by
      intro s hs
      rw [glove_number_complete_graph_pos_hs_update K φ hb e p t s (hs p (List.mem_cons_self ..)).1
        (hs p (List.mem_cons_self ..)).2]
      exact hinv s (fun q hq => hs q (List.mem_cons_of_mem p hq))
    refine CleanHandshakeSeq.cons _ _ _ hclean ?_
    exact ih (p :: P) (handshake_update_contam (glove_number_complete_graph_pos_hs K φ hb e p) t) hL'
      (fun q hq => by
        intro hq2
        rcases List.mem_cons.mp hq2 with rfl | hq2'
        · exact hpL hq
        · exact hdisj q (List.mem_cons_of_mem p hq) hq2') hinv'

/-- For n ≥ 2, the glove number of K_n is at least 1. -/
theorem glove_number_complete_graph_pos (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ glove_number (SimpleGraph.completeGraph (Fin n)) := by
  have hn0 : 0 < n := by omega
  have hex : ∃ k, has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k := by
    let φ : Fin (n * n) → ℕ := fun k => k.val
    have hφ : Function.Injective φ := fun a b h => Fin.ext h
    have hb : ∀ k : Fin (n * n), 2 * φ k + 1 < 2 * (n * n) := by
      intro k
      have := k.isLt
      simp only [φ]
      omega
    let e : Fin (n * n) → Fin n × Fin n := fun k =>
      (⟨k.val / n, (Nat.div_lt_iff_lt_mul hn0).mpr k.isLt⟩, ⟨k.val % n, Nat.mod_lt _ hn0⟩)
    have hclean := glove_number_complete_graph_pos_clean (K := 2 * (n * n)) (φ := φ) hφ hb e
      (List.finRange (n * n)) [] (fun _ => ∅) (List.nodup_finRange _) (by simp) (by simp)
    refine ⟨2 * (n * n), List.map (glove_number_complete_graph_pos_hs (2 * (n * n)) φ hb e)
      (List.finRange (n * n)), hclean, ?_⟩
    have hk' : ∀ i j : Fin n, i.val * n + j.val < n * n := by
      intro i j
      have h1 : i.val * n + j.val < (i.val + 1) * n := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt))
    have key : ∀ i j : Fin n, Sym2.mk i j ∈ (SimpleGraph.completeGraph (Fin n)).edgeSet →
        ∃ h ∈ List.map (glove_number_complete_graph_pos_hs (2 * (n * n)) φ hb e)
          (List.finRange (n * n)), handshake_edge h = Sym2.mk i j := by
      intro i j _
      have hdiv : (i.val * n + j.val) / n = i.val := by
        have h1 : i.val * n + j.val = j.val + n * i.val := by rw [Nat.mul_comm i.val n]; omega
        rw [h1, Nat.add_mul_div_left j.val i.val hn0, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
      have hmod : (i.val * n + j.val) % n = j.val := by
        rw [Nat.mul_comm i.val n, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]
      have hek : e ⟨i.val * n + j.val, hk' i j⟩ = (i, j) := by
        simp only [e, hdiv, hmod]
      refine ⟨glove_number_complete_graph_pos_hs (2 * (n * n)) φ hb e ⟨i.val * n + j.val, hk' i j⟩,
        List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩, ?_⟩
      rw [glove_number_complete_graph_pos_hs_edge, hek]
    intro edge hedge
    exact Sym2.ind key edge hedge
  have hne : {k | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k}.Nonempty := hex
  have hpos : sInf {k | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k} ≠ 0 := by
    intro h
    rcases Nat.sInf_eq_zero.mp h with h0 | hemp
    · exact glove_number_complete_graph_no_zero_gloves n hn h0
    · rw [hemp] at hne
      exact Set.not_nonempty_empty hne
  show 1 ≤ sInf {k | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k}
  omega
