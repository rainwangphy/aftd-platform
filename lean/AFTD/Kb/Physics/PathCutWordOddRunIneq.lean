import AFTD.Prelude
import AFTD.Kb.Physics.PathCutWord
import AFTD.Kb.Physics.OddRunCount
import AFTD.Kb.Physics.PathCertOddRunIneq
import AFTD.Kb.Physics.PathCertWord
import AFTD.Kb.Physics.PathCertWordEqCutWord
import AFTD.Kb.Physics.IsFourPartition
import AFTD.Kb.Physics.OddRunAux
import AFTD.Kb.Physics.PathCertSign
import AFTD.Kb.Physics.PathCertMask

/-!
# path_cut_word_odd_run_ineq

Topic: quantum_mechanics   Node: 0347a50ccc2e

Provenance: helper lemma. step towards claw_free_tree_graph_state_mmi

For a four-partition A,B,C,D of the vertices of the path P_n, the sum of the numbers of maximal odd-length crossing runs for A, B, C and D is at most the corresponding sum for A ∪ B, A ∪ C and B ∪ C.
-/

open scoped Classical BigOperators

lemma cut_word_compl_scratch (n : ℕ) (S : Finset (Fin n)) :
    path_cut_word n Sᶜ = path_cut_word n S := by
  unfold path_cut_word
  apply congrArg List.ofFn
  funext k
  simp only [Finset.mem_compl, decide_not]
  cases (decide ((⟨k.val, by omega⟩ : Fin n) ∈ S)) <;>
    cases (decide ((⟨k.val + 1, by omega⟩ : Fin n) ∈ S)) <;> decide

/-- Odd crossing runs of A,B,C,D are dominated by those of AB,AC,BC. -/
theorem path_cut_word_odd_run_ineq (n : ℕ) (A B C D : Finset (Fin n))
    (hpart : is_four_partition A B C D) :
    odd_run_count (path_cut_word n A) + odd_run_count (path_cut_word n B) +
        odd_run_count (path_cut_word n C) + odd_run_count (path_cut_word n D) ≤
      odd_run_count (path_cut_word n (A ∪ B)) + odd_run_count (path_cut_word n (A ∪ C)) +
        odd_run_count (path_cut_word n (B ∪ C)) := by
  classical
  rcases hpart with ⟨hAB,hAC,hAD,hBC,hBD,hCD,hall⟩
  have hD : D = (A ∪ B ∪ C)ᶜ := by
    ext v
    have hcover : v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D := by
      have hh : v ∈ A ∪ B ∪ C ∪ D := by rw [hall]; simp
      simpa only [Finset.mem_union, or_assoc] using hh
    have hda := Finset.disjoint_left.mp hAD
    have hdb := Finset.disjoint_left.mp hBD
    have hdc := Finset.disjoint_left.mp hCD
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    constructor
    · intro hd
      exact ⟨⟨fun ha => hda ha hd, fun hb => hdb hb hd⟩, fun hc => hdc hc hd⟩
    · intro h
      rcases h with ⟨⟨ha,hb⟩,hc⟩
      rcases hcover with ha' | hb' | hc' | hd
      · exact False.elim (ha ha')
      · exact False.elim (hb hb')
      · exact False.elim (hc hc')
      · exact hd
  cases n with
  | zero => simp [path_cut_word, odd_run_count, odd_run_aux]
  | succ m =>
    let color : Fin (m+1) → Fin 4 := fun v => if v ∈ A then 0 else if v ∈ B then 1 else if v ∈ C then 2 else 3
    let sets : Fin 7 → Finset (Fin (m+1)) := ![A,B,C,A ∪ B,A ∪ C,B ∪ C,A ∪ B ∪ C]
    have hmask (j : Fin 7) :
        (Finset.univ.filter fun v => Nat.testBit (pathCertMask j) (color v).val) = sets j := by
      fin_cases j <;> ext v : 1 <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;>
        by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;> by_cases hc : v ∈ C <;>
        simp_all [sets, color, pathCertMask, Finset.disjoint_left] <;> decide
    have hm (j : Fin 7) :
        pathCertWord (color ⟨0, by omega⟩)
          (List.ofFn fun k : Fin ((m+1)-1) => color ⟨k.val+1, by omega⟩) j =
          path_cut_word (m+1) (sets j) := by
      rw [← hmask j]
      exact path_cert_word_eq_cut_word (m+1) (by omega) color j
    have hw := pathCertOddRunIneq (color ⟨0, by omega⟩)
      (List.ofFn fun k : Fin ((m+1)-1) => color ⟨k.val+1, by omega⟩)
    simp_rw [hm] at hw
    have hcomp : path_cut_word (m+1) D = path_cut_word (m+1) (A ∪ B ∪ C) := by
      rw [hD]
      exact cut_word_compl_scratch _ _
    simp only [Finset.union_assoc] at hcomp
    simp [Fin.sum_univ_succ, pathCertSign, sets, ← hcomp] at hw
    omega
