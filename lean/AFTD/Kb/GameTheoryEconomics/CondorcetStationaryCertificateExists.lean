import AFTD.Prelude

/-!
# condorcet_stationary_certificate_exists

Topic: social_choice   Node: fa0be35d5115

Provenance: helper lemma. step towards condorcet_stationary_weight_restriction_obstruction

Explicit constructive witnesses (S, f, d, next, p) on 8 candidates and 56 triples, verified by finite decision, satisfying the subset properties, coverage of all triples, transition law, the C=139, K=70 local potential inequality, and the unrestricted 3-claim certificate of total weight 3 with full-set value 1.
-/

def condorcet_stationary_certificate_exists_SList : List (Finset (Fin 8)) :=
  [{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,1,6},{0,1,7},
   {0,2,3},{0,2,4},{0,2,5},{0,2,6},{0,2,7},
   {0,3,4},{0,3,5},{0,3,6},{0,3,7},
   {0,4,5},{0,4,6},{0,4,7},
   {0,5,6},{0,5,7},{0,6,7},
   {1,2,3},{1,2,4},{1,2,5},{1,2,6},{1,2,7},
   {1,3,4},{1,3,5},{1,3,6},{1,3,7},
   {1,4,5},{1,4,6},{1,4,7},
   {1,5,6},{1,5,7},{1,6,7},
   {2,3,4},{2,3,5},{2,3,6},{2,3,7},
   {2,4,5},{2,4,6},{2,4,7},
   {2,5,6},{2,5,7},{2,6,7},
   {3,4,5},{3,4,6},{3,4,7},
   {3,5,6},{3,5,7},{3,6,7},
   {4,5,6},{4,5,7},{4,6,7},{5,6,7}]

def condorcet_stationary_certificate_exists_fList : List (Fin 8) :=
  [7,7,7,7,7,6,7,7,7,7,6,7,7,7,6,7,7,6,7,6,5,0,0,0,0,6,0,0,0,6,0,0,6,0,6,5,
   1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,4]

def condorcet_stationary_certificate_exists_dList : List (Fin 3 → Fin 8) :=
  [![0,1,2],![0,1,3],![0,1,4],![0,1,5],![0,1,6],![0,1,7],
   ![0,2,3],![0,2,4],![0,2,5],![0,2,6],![0,2,7],
   ![0,3,4],![0,3,5],![0,3,6],![0,3,7],
   ![0,4,5],![0,4,6],![0,4,7],
   ![0,5,6],![0,5,7],![0,6,7],
   ![1,2,3],![1,2,4],![1,2,5],![1,2,6],![1,2,7],
   ![1,3,4],![1,3,5],![1,3,6],![1,3,7],
   ![1,4,5],![1,4,6],![1,4,7],
   ![1,5,6],![1,5,7],![1,6,7],
   ![2,3,4],![2,3,5],![2,3,6],![2,3,7],
   ![2,4,5],![2,4,6],![2,4,7],
   ![2,5,6],![2,5,7],![2,6,7],
   ![3,4,5],![3,4,6],![3,4,7],
   ![3,5,6],![3,5,7],![3,6,7],
   ![4,5,6],![4,5,7],![4,6,7],![5,6,7]]

def condorcet_stationary_certificate_exists_nList : List (Fin 3 → Fin 56) :=
  [![25,10,5],![29,14,5],![32,17,5],![34,19,5],![35,20,5],![35,20,4],
   ![39,14,10],![42,17,10],![44,19,10],![45,20,10],![45,20,9],
   ![48,17,14],![50,19,14],![51,20,14],![51,20,13],
   ![53,19,17],![54,20,17],![54,20,16],
   ![55,20,19],![55,20,18],![55,19,18],
   ![6,1,0],![7,2,0],![8,3,0],![9,4,0],![45,35,24],
   ![11,2,1],![12,3,1],![13,4,1],![51,35,28],
   ![15,3,2],![16,4,2],![54,35,31],
   ![18,4,3],![55,35,33],![55,34,33],
   ![26,22,21],![27,23,21],![28,24,21],![29,25,21],
   ![30,23,22],![31,24,22],![32,25,22],
   ![33,24,23],![34,25,23],![35,25,24],
   ![40,37,36],![41,38,36],![42,39,36],
   ![43,38,37],![44,39,37],![45,39,38],
   ![49,47,46],![50,48,46],![51,48,47],![54,53,52]]

def condorcet_stationary_certificate_exists_pList : List ℕ :=
  [0,6,12,20,20,20,13,18,24,24,24,28,33,33,33,44,44,44,55,55,55,29,33,37,37,28,
   38,42,42,36,48,48,45,54,55,55,56,59,59,53,62,62,58,65,63,63,82,82,78,84,81,81,
   105,103,103,126]

def condorcet_stationary_certificate_exists_S : Fin 56 → Finset (Fin 8) :=
  fun i => condorcet_stationary_certificate_exists_SList.getD i.val ∅

def condorcet_stationary_certificate_exists_f : Fin 56 → Fin 8 :=
  fun i => condorcet_stationary_certificate_exists_fList.getD i.val 0

def condorcet_stationary_certificate_exists_d : Fin 56 → Fin 3 → Fin 8 :=
  fun i => condorcet_stationary_certificate_exists_dList.getD i.val (fun _ => 0)

def condorcet_stationary_certificate_exists_next : Fin 56 → Fin 3 → Fin 56 :=
  fun i => condorcet_stationary_certificate_exists_nList.getD i.val (fun _ => 0)

def condorcet_stationary_certificate_exists_p : Fin 56 → ℕ :=
  fun i => condorcet_stationary_certificate_exists_pList.getD i.val 0

def condorcet_stationary_certificate_exists_w : Fin 56 → ℕ :=
  fun i => if i = 18 ∨ i = 19 ∨ i = 20 then 1 else 0

def condorcet_stationary_certificate_exists_H : Finset (Fin 8) → ℕ :=
  fun A => if ({5,6,7} : Finset (Fin 8)) ⊆ A then 1 else 0

/-- Existence and verification of concrete 56-triple reset selector witnesses and potentials on 8 candidates. -/
theorem condorcet_stationary_certificate_exists :
    ∃ (S : Fin 56 → Finset (Fin 8)) (f : Fin 56 → Fin 8)
      (d : Fin 56 → Fin 3 → Fin 8) (next : Fin 56 → Fin 3 → Fin 56)
      (p : Fin 56 → ℕ),
      (∀ i, (S i).card = 3 ∧ f i ∉ S i ∧ Function.Injective (d i) ∧
        S i = Finset.univ.image (d i)) ∧
      (∀ T : Finset (Fin 8), T.card = 3 → ∃ i, S i = T) ∧
      (∀ i j, S (next i j) = insert (f i) ((S i).erase (d i j))) ∧
      (∀ i, 70 + 3 * p i ≤ 139 * (if ∀ b ∈ S i, f i < b then 1 else 0) + ∑ k : Fin 3, p (next i k)) ∧
      (∃ (w : Fin 56 → ℕ) (H : Finset (Fin 8) → ℕ),
        (∀ A : Finset (Fin 8), ∀ a ∈ A,
          (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
        2 * H Finset.univ < ∑ i, w i) := by
  refine ⟨condorcet_stationary_certificate_exists_S,
          condorcet_stationary_certificate_exists_f,
          condorcet_stationary_certificate_exists_d,
          condorcet_stationary_certificate_exists_next,
          condorcet_stationary_certificate_exists_p,
          by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨condorcet_stationary_certificate_exists_w,
         condorcet_stationary_certificate_exists_H,
         by decide, by decide⟩
