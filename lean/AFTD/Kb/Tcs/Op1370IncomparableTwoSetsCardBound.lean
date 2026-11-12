import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented

/-!
# op_1370_incomparable_two_sets_card_bound

Topic: combinatorics   Node: 9c56717061af

Provenance: helper lemma. Counting lemma for OP-1370 and arXiv:2611.12199, Conjecture 4.3.

On an n-element ground set with n at least three, let A and B be incomparable subsets, and let F be an uncomplemented family every member of which is incomparable to both A and B. Then twice the cardinality of F plus six is at most 2 to the power n.
-/

open Finset
set_option maxHeartbeats 800000

lemma op_1370_pair_count_missing_six (n : ℕ) (hn : 3 ≤ n)
    (F : Finset (Finset (Fin n))) (hu : is_uncomplemented F)
    (x y : Fin n) (hxy : x ≠ y)
    (h0 : (∅ : Finset (Fin n)) ∉ F)
    (h1 : (univ : Finset (Fin n)) ∉ F)
    (hx : ({x} : Finset (Fin n)) ∉ F)
    (hy : ({y} : Finset (Fin n)) ∉ F)
    (hxc : ({x} : Finset (Fin n))ᶜ ∉ F)
    (hyc : ({y} : Finset (Fin n))ᶜ ∉ F) :
    2 * F.card + 6 ≤ 2 ^ n := by
  classical
  let G : Finset (Finset (Fin n)) := F.image compl
  have hdis : Disjoint F G := by
    rw [Finset.disjoint_left]
    intro s hs hsg
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hsg
    subst s
    exact hu t ht hs
  have hG : G.card = F.card := Finset.card_image_of_injective _ compl_injective
  have hneq1 : ({x} : Finset (Fin n)) ≠ ({y} : Finset (Fin n)) := by simpa using hxy
  have hneq2 : ({x} : Finset (Fin n))ᶜ ≠ ({y} : Finset (Fin n))ᶜ := by simpa using hneq1
  have hlarge : 2 ≤ n - 1 := by omega
  have hcc (z : Fin n) : (({z} : Finset (Fin n))ᶜ).card = n - 1 := by rw [Finset.card_compl]; simp
  have hc0 (z : Fin n) : ({z} : Finset (Fin n))ᶜ ≠ ∅ := by
    intro h
    have := congrArg Finset.card h
    simp [hcc] at this
    omega
  have hc1 (z : Fin n) : ({z} : Finset (Fin n))ᶜ ≠ univ := by
    intro h
    have hmem : z ∈ ({z} : Finset (Fin n))ᶜ := by rw [h]; simp
    simpa using hmem
  have hcs (z w : Fin n) : ({z} : Finset (Fin n))ᶜ ≠ {w} := by
    intro h
    have := congrArg Finset.card h
    simp [hcc] at this
    omega
  have hEU : (∅ : Finset (Fin n)) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  have hUS (z : Fin n) : (univ : Finset (Fin n)) ≠ {z} := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  let B : Finset (Finset (Fin n)) := {∅, univ, {x}, {y}, ({x} : Finset (Fin n))ᶜ, ({y} : Finset (Fin n))ᶜ}
  have hb : B.card = 6 := by
    simp [B, Finset.card_insert_eq_ite, hEU, hUS, hneq1, hneq2, hc0, hc1, hcs, Ne.symm hneq1, Ne.symm hneq2,
      Ne.symm (hc0 x), Ne.symm (hc0 y), Ne.symm (hc1 x), Ne.symm (hc1 y),
      Ne.symm (hcs x x), Ne.symm (hcs x y), Ne.symm (hcs y x), Ne.symm (hcs y y), hn]
  have hBF : Disjoint B F := by
    rw [Finset.disjoint_left]
    intro s hs hsF
    simp only [B, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> contradiction
  have hBG : Disjoint B G := by
    rw [Finset.disjoint_left]
    intro s hs hsG
    obtain ⟨t, ht, hts⟩ := mem_image.mp hsG
    have htc : t = sᶜ := by rw [← hts, compl_compl]
    subst t
    simp only [B, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hd : Disjoint B (F ∪ G) := disjoint_union_right.mpr ⟨hBF, hBG⟩
  have hcard := Finset.card_le_univ (B ∪ (F ∪ G))
  rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hdis, hb, hG] at hcard
  have huniv : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    rw [← Finset.card_univ, ← Finset.powerset_univ, Finset.card_powerset]
    simp
  rw [huniv] at hcard
  omega

lemma op_1370_incomparable_two_sets_card_bound
    (n : ℕ) (hn : 3 ≤ n) (A B : Finset (Fin n))
    (hab : ¬ A ⊆ B) (hba : ¬ B ⊆ A)
    (F : Finset (Finset (Fin n))) (hu : is_uncomplemented F)
    (hFA : ∀ S ∈ F, ¬ S ⊆ A) (hAF : ∀ S ∈ F, ¬ A ⊆ S)
    (hFB : ∀ S ∈ F, ¬ S ⊆ B) (hBF : ∀ S ∈ F, ¬ B ⊆ S) :
    2 * F.card + 6 ≤ 2 ^ n := by
  classical
  obtain ⟨x, hxA, hxB⟩ := Finset.not_subset.mp hab
  obtain ⟨y, hyB, hyA⟩ := Finset.not_subset.mp hba
  have hxy : x ≠ y := by intro h; subst y; exact hxB hyB
  apply op_1370_pair_count_missing_six n hn F hu x y hxy
  · intro h; exact hFA ∅ h (empty_subset A)
  · intro h; exact hAF univ h (subset_univ A)
  · intro h; exact hFA {x} h (singleton_subset_iff.mpr hxA)
  · intro h; exact hFB {y} h (singleton_subset_iff.mpr hyB)
  · intro h; apply hBF _ h; intro z hz; simp only [mem_compl, mem_singleton]; intro hzx; subst z; exact hxB hz
  · intro h; apply hAF _ h; intro z hz; simp only [mem_compl, mem_singleton]; intro hzy; subst z; exact hyA hz
