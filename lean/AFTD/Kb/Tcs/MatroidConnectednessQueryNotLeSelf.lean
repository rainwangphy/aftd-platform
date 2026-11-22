import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.ExistsMatroidOfIndepTable
import AFTD.Kb.Tcs.MatroidConnectednessQueryNotLeOfSensitive
import AFTD.Kb.Tcs.NotMatroidConnectedOfIndepGround
import AFTD.Kb.Tcs.MatroidConnected

/-!
# matroid_connectedness_query_not_le_self

Topic: algorithms   Node: 96295369925f

Provenance: original. Related work: Lower bound for OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier)). Proposition 2 of the paper proves that at least n queries are needed (the rank-1 uniform matroid and its n one-loop neighbours); this is one more, from the n-element circuit.

Here matroid_connectedness_query_le n q means: some deterministic independence-query decision tree of depth at most q decides, for every matroid with ground set Fin n, whether it is connected (any two distinct elements lie in a common circuit). For every n ≥ 2, n independence queries do not suffice to decide connectedness of matroids on n elements: matroid_connectedness_query_le n n fails, i.e. at least n + 1 queries are needed.
-/

open Matroid Set

def mcqnlsUnifIndep (n : ℕ) : Finset (Fin n) → Prop := fun I => I.card ≤ n - 1

lemma mcqnlsUnifIndep_empty (n : ℕ) : mcqnlsUnifIndep n ∅ := by
  simp [mcqnlsUnifIndep]

lemma mcqnlsUnifIndep_subset {n : ℕ} {I J : Finset (Fin n)}
    (hJ : mcqnlsUnifIndep n J) (hIJ : I ⊆ J) : mcqnlsUnifIndep n I := by
  simp only [mcqnlsUnifIndep] at hJ ⊢
  exact le_trans (Finset.card_le_card hIJ) hJ

lemma mcqnlsUnifIndep_aug {n : ℕ} {I J : Finset (Fin n)}
    (hI : mcqnlsUnifIndep n I) (hJ : mcqnlsUnifIndep n J) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ mcqnlsUnifIndep n (insert e I) := by
  simp only [mcqnlsUnifIndep] at hI hJ ⊢
  obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨e, heJ, heI, by rw [Finset.card_insert_of_notMem heI]; omega⟩

noncomputable def mcqnlsUnif (n : ℕ) : Matroid (Fin n) :=
  (IndepMatroid.ofFinset (E := Set.univ) (mcqnlsUnifIndep n)
    (mcqnlsUnifIndep_empty n)
    (fun _ _ hJ hIJ => mcqnlsUnifIndep_subset hJ hIJ)
    (fun _ _ hI hJ hlt => mcqnlsUnifIndep_aug hI hJ hlt)
    (by intro I _; exact subset_univ (I : Set (Fin n)))).matroid

lemma mcqnlsUnif_ground (n : ℕ) : (mcqnlsUnif n).E = Set.univ := rfl

lemma mcqnlsUnif_indep_finset {n : ℕ} {I : Finset (Fin n)} :
    (mcqnlsUnif n).Indep (I : Set (Fin n)) ↔ I.card ≤ n - 1 := by
  simp [mcqnlsUnif, mcqnlsUnifIndep]

lemma mcqnlsUnif_indep_iff {n : ℕ} (hn : 1 ≤ n) {I : Set (Fin n)} :
    (mcqnlsUnif n).Indep I ↔ I ≠ Set.univ := by
  rw [mcqnlsUnif, IndepMatroid.matroid_indep_iff, IndepMatroid.ofFinset_indep']
  constructor
  · intro h hI
    subst hI
    have h1 := h Finset.univ (by simp)
    simp only [mcqnlsUnifIndep] at h1
    have h2 : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega
  · intro hI J hJ
    simp only [mcqnlsUnifIndep]
    by_contra hc
    push Not at hc
    have hJn : J.card = n := by
      have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
      omega
    have hJuniv : J = Finset.univ := Finset.eq_univ_of_card J (by simpa using hJn)
    have hsub : (Set.univ : Set (Fin n)) ⊆ I := by
      rw [← Finset.coe_univ, ← hJuniv]; exact hJ
    exact hI (subset_antisymm (subset_univ I) hsub)

lemma mcqnlsUnif_connected {n : ℕ} (hn : 2 ≤ n) : matroid_connected (mcqnlsUnif n) := by
  intro e he f hf
  refine Or.inr ⟨Set.univ, ?_, trivial, trivial⟩
  rw [Matroid.isCircuit_iff]
  constructor
  · rw [Matroid.dep_iff]
    refine ⟨?_, subset_univ _⟩
    intro hI
    exact ((mcqnlsUnif_indep_iff (by omega) (I := Set.univ)).mp hI) rfl
  · intro D hD hDsub
    rw [Matroid.dep_iff] at hD
    by_contra hne
    exact hD.1 ((mcqnlsUnif_indep_iff (by omega) (I := D)).mpr hne)

def mcqnlsExclIndep (n : ℕ) (e : Fin n) : Finset (Fin n) → Prop :=
  fun I => I.card ≤ n - 1 ∧ I ≠ Finset.univ.erase e

lemma mcqnlsEraseCard {n : ℕ} (e : Fin n) :
    (Finset.univ.erase e : Finset (Fin n)).card = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ e)]; simp

lemma mcqnlsExclIndep_empty {n : ℕ} (hn : 2 ≤ n) (e : Fin n) : mcqnlsExclIndep n e ∅ := by
  refine ⟨by simp [mcqnlsExclIndep], ?_⟩
  intro h
  have hc : (Finset.univ.erase e : Finset (Fin n)).card = 0 := by rw [← h]; simp
  rw [mcqnlsEraseCard] at hc; omega

lemma mcqnlsExclIndep_subset {n : ℕ} {e : Fin n} {I J : Finset (Fin n)}
    (hJ : mcqnlsExclIndep n e J) (hIJ : I ⊆ J) : mcqnlsExclIndep n e I := by
  obtain ⟨hJc, hJne⟩ := hJ
  refine ⟨le_trans (Finset.card_le_card hIJ) hJc, ?_⟩
  intro hI
  apply hJne
  have hbJ : Finset.univ.erase e ⊆ J := hI ▸ hIJ
  have hcJ : J.card ≤ (Finset.univ.erase e : Finset (Fin n)).card := by
    rw [mcqnlsEraseCard]; exact hJc
  exact (Finset.eq_of_subset_of_card_le hbJ hcJ).symm

lemma mcqnlsExclIndep_aug {n : ℕ} {e : Fin n} {I J : Finset (Fin n)}
    (hI : mcqnlsExclIndep n e I) (hJ : mcqnlsExclIndep n e J) (hlt : I.card < J.card) :
    ∃ f ∈ J, f ∉ I ∧ mcqnlsExclIndep n e (insert f I) := by
  obtain ⟨hIc, hIne⟩ := hI
  obtain ⟨hJc, hJne⟩ := hJ
  by_cases h : ∃ f ∈ J, f ∉ I ∧ insert f I ≠ Finset.univ.erase e
  · obtain ⟨f, hfJ, hfI, hfb⟩ := h
    exact ⟨f, hfJ, hfI, by rw [Finset.card_insert_of_notMem hfI]; omega, hfb⟩
  · exfalso
    push Not at h
    obtain ⟨f0, hf0J, hf0I⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hb0 : insert f0 I = Finset.univ.erase e := h f0 hf0J hf0I
    have hJb : J ⊆ Finset.univ.erase e := by
      intro x hxJ
      by_cases hxI : x ∈ I
      · rw [← hb0]; exact Finset.mem_insert_of_mem hxI
      · rw [← h x hxJ hxI]; exact Finset.mem_insert_self x I
    have hJble : J.card ≤ (Finset.univ.erase e : Finset (Fin n)).card :=
      Finset.card_le_card hJb
    have hcJ : J.card = (Finset.univ.erase e : Finset (Fin n)).card := by
      have hins : (insert f0 I : Finset (Fin n)).card = I.card + 1 :=
        Finset.card_insert_of_notMem hf0I
      rw [hb0] at hins; omega
    exact hJne (Finset.eq_of_subset_of_card_le hJb (le_of_eq hcJ.symm))

noncomputable def mcqnlsExcl (n : ℕ) (hn : 2 ≤ n) (e : Fin n) : Matroid (Fin n) :=
  (IndepMatroid.ofFinset (E := Set.univ) (mcqnlsExclIndep n e)
    (mcqnlsExclIndep_empty hn e)
    (fun _ _ hJ hIJ => mcqnlsExclIndep_subset hJ hIJ)
    (fun _ _ hI hJ hlt => mcqnlsExclIndep_aug hI hJ hlt)
    (by intro I _; exact subset_univ (I : Set (Fin n)))).matroid

lemma mcqnlsExcl_ground {n : ℕ} (hn : 2 ≤ n) (e : Fin n) :
    (mcqnlsExcl n hn e).E = Set.univ := rfl

lemma mcqnlsExcl_indep_finset {n : ℕ} (hn : 2 ≤ n) (e : Fin n) {I : Finset (Fin n)} :
    (mcqnlsExcl n hn e).Indep (I : Set (Fin n)) ↔
      I.card ≤ n - 1 ∧ I ≠ Finset.univ.erase e := by
  simp [mcqnlsExcl, mcqnlsExclIndep]

lemma mcqnlsExcl_indep_iff {n : ℕ} (hn : 2 ≤ n) (e : Fin n) {I : Set (Fin n)} :
    (mcqnlsExcl n hn e).Indep I ↔ I ≠ Set.univ ∧ I ≠ (Finset.univ.erase e : Set (Fin n)) := by
  rw [mcqnlsExcl, IndepMatroid.matroid_indep_iff, IndepMatroid.ofFinset_indep']
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hI
      subst hI
      have h1 := h Finset.univ (by simp)
      simp only [mcqnlsExclIndep] at h1
      have h2 : (Finset.univ : Finset (Fin n)).card = n := by simp
      omega
    · intro hI
      have h1 := h (Finset.univ.erase e) (by rw [hI])
      simp only [mcqnlsExclIndep] at h1
      exact h1.2 rfl
  · intro ⟨hU, hB⟩ J hJ
    constructor
    · by_contra hc
      push Not at hc
      have hJn : J.card = n := by
        have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
        omega
      have hJuniv : J = Finset.univ := Finset.eq_univ_of_card J (by simpa using hJn)
      apply hU
      have hsub : (Set.univ : Set (Fin n)) ⊆ I := by
        rw [← Finset.coe_univ, ← hJuniv]; exact hJ
      exact subset_antisymm (subset_univ I) hsub
    · intro hJb
      apply hB
      have hsub : (Finset.univ.erase e : Set (Fin n)) ⊆ I := by rw [← hJb]; exact hJ
      have hsub' : (Set.univ \ {e} : Set (Fin n)) ⊆ I := by
        rw [Finset.coe_erase, Finset.coe_univ] at hsub; exact hsub
      apply subset_antisymm ?_ hsub
      intro x hx
      rw [Finset.coe_erase, Finset.coe_univ]
      refine ⟨trivial, ?_⟩
      intro hxe
      apply hU
      apply subset_antisymm (subset_univ I)
      intro y _
      by_cases hy : y = e
      · rw [hy]; exact hxe ▸ hx
      · exact hsub' (by simp [hy])

lemma mcqnlsExcl_isCircuit_iff {n : ℕ} (hn : 2 ≤ n) (e : Fin n) {C : Set (Fin n)} :
    (mcqnlsExcl n hn e).IsCircuit C ↔ C = (Finset.univ.erase e : Set (Fin n)) := by
  rw [Matroid.isCircuit_iff]
  constructor
  · rintro ⟨hdep, hmin⟩
    have hcases : C = Set.univ ∨ C = (Finset.univ.erase e : Set (Fin n)) := by
      by_contra hc
      push Not at hc
      exact hdep.1 ((mcqnlsExcl_indep_iff hn e).mpr hc)
    rcases hcases with h | h
    · exfalso
      have hdepb : (mcqnlsExcl n hn e).Dep (Finset.univ.erase e : Set (Fin n)) := by
        rw [Matroid.dep_iff]
        refine ⟨?_, subset_univ _⟩
        intro hind
        exact ((mcqnlsExcl_indep_iff hn e).mp hind).2 rfl
      have hbC : (Finset.univ.erase e : Set (Fin n)) ⊆ C := by rw [h]; exact subset_univ _
      have heq := hmin hdepb hbC
      rw [h] at heq
      have hmem : e ∈ (Finset.univ.erase e : Set (Fin n)) := by
        rw [heq]; exact mem_univ e
      simp at hmem
    · exact h
  · intro hC
    subst hC
    constructor
    · rw [Matroid.dep_iff]
      refine ⟨?_, subset_univ _⟩
      intro hind
      exact ((mcqnlsExcl_indep_iff hn e).mp hind).2 rfl
    · intro D hD hDC
      rw [Matroid.dep_iff] at hD
      by_contra hne
      have hDuniv : D = Set.univ := by
        by_contra hnu
        exact hD.1 ((mcqnlsExcl_indep_iff hn e).mpr ⟨hnu, hne⟩)
      rw [hDuniv] at hDC
      exact absurd (hDC (mem_univ e)) (by simp)

lemma mcqnlsExcl_not_connected {n : ℕ} (hn : 2 ≤ n) (e : Fin n) :
    ¬ matroid_connected (mcqnlsExcl n hn e) := by
  intro hconn
  have hcard : ({e} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    simp; omega
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hfe : f ≠ e := by simpa using hf
  have heE : e ∈ (mcqnlsExcl n hn e).E := by rw [mcqnlsExcl_ground hn]; exact mem_univ e
  have hfE : f ∈ (mcqnlsExcl n hn e).E := by rw [mcqnlsExcl_ground hn]; exact mem_univ f
  rcases hconn e heE f hfE with rfl | ⟨C, hC, heC, -⟩
  · exact hfe rfl
  · rw [mcqnlsExcl_isCircuit_iff hn e] at hC
    rw [hC] at heC
    simp at heC

lemma mcqnlsFreeOn_not_connected {n : ℕ} (hn : 2 ≤ n) :
    ¬ matroid_connected (freeOn (Set.univ : Set (Fin n))) := by
  refine not_matroid_connected_of_indep_ground (freeOn (Set.univ : Set (Fin n)))
    ⟨0, by omega⟩ ⟨1, by omega⟩ ?_ ?_ ?_ ?_
  · rw [freeOn_ground]; exact mem_univ _
  · rw [freeOn_ground]; exact mem_univ _
  · simp
  · rw [freeOn_ground]; exact freeOn_indep (subset_refl _)

lemma mcqnlsFamilyCard {n : ℕ} (_hn : 2 ≤ n) :
    (insert (Finset.univ : Finset (Fin n))
      (Finset.univ.image (fun e : Fin n => Finset.univ.erase e))).card = n + 1 := by
  have hinj : Function.Injective (fun e : Fin n => (Finset.univ.erase e : Finset (Fin n))) := by
    intro e f hef
    by_contra hne
    have hef' : (Finset.univ.erase e : Finset (Fin n)) = Finset.univ.erase f := hef
    have hmem : e ∈ (Finset.univ.erase f : Finset (Fin n)) := by simp [Finset.mem_erase, hne]
    rw [← hef'] at hmem; simp at hmem
  have hcard_img : (Finset.univ.image (fun e : Fin n => Finset.univ.erase e)).card = n := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hnotmem : (Finset.univ : Finset (Fin n)) ∉
      Finset.univ.image (fun e : Fin n => Finset.univ.erase e) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨e, -, he⟩ := h
    have hmem : e ∈ (Finset.univ.erase e : Finset (Fin n)) := by rw [he]; exact Finset.mem_univ e
    simp at hmem
  rw [Finset.card_insert_of_notMem hnotmem, hcard_img]

theorem matroid_connectedness_query_not_le_self (n : ℕ) (hn : 2 ≤ n) :
    ¬ matroid_connectedness_query_le n n := by
  refine matroid_connectedness_query_not_le_of_sensitive (mcqnlsUnif n) (mcqnlsUnif_ground n)
    (mcqnlsUnif_connected hn)
    (insert (Finset.univ : Finset (Fin n))
      (Finset.univ.image (fun e : Fin n => Finset.univ.erase e))) ?_ n ?_
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_image] at hS
    rcases hS with rfl | ⟨e, -, he⟩
    · refine ⟨freeOn (Set.univ : Set (Fin n)), freeOn_ground,
        mcqnlsFreeOn_not_connected hn, ?_⟩
      intro S' hS'
      rw [freeOn_indep_iff, mcqnlsUnif_indep_finset]
      refine ⟨fun _ => ?_, fun _ => subset_univ _⟩
      have hle : S'.card ≤ n := by simpa using Finset.card_le_univ S'
      have hne : S'.card ≠ n := fun hc =>
        hS' (Finset.eq_univ_of_card S' (by simpa using hc))
      omega
    · rw [← he]
      refine ⟨mcqnlsExcl n hn e, mcqnlsExcl_ground hn e,
        mcqnlsExcl_not_connected hn e, ?_⟩
      intro S' hS'
      rw [mcqnlsExcl_indep_finset hn e, mcqnlsUnif_indep_finset]
      simp [hS']
  · rw [mcqnlsFamilyCard hn]; omega
