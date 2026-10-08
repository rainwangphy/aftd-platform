import AFTD.Prelude
import AFTD.Kb.Tcs.SubsetSumToPartitionPartition
import AFTD.Kb.Tcs.SubsetSumToPartitionSubsetSum
import AFTD.Kb.Tcs.SubsetSumToPartitionPartitionWeight

/-!
# SubsetSumToPartition.SubsetSumToPartitionSoundness

Topic: np_completeness   Node: 7bf35b1371b2

Provenance: formalization of a published result. Source: Soundness of the Subset Sum to Partition reduction, as formalized in TCSlib (`SubsetSumToPartition.SubsetSumToPartitionSoundness`). Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean (Apache-2.0); 1 verbatim; compiled here.

Soundness of the Subset Sum to Partition reduction. Let $w : \bbn^{U}$ be a weight function on a finite type $U$, and let $T \in \bbn$ be a
target with $T \le \sum_{a} w(a)$. Form the reduction weight function on the augmented
type $U \oplus \mathrm{Bool}$, which assigns each original item the weight $w(a)$, the
first dummy item the weight $2\sum_a w(a) - T$, and the second dummy item the weight
$\sum_a w(a) + T$. Then, if this augmented instance is a yes-instance of Partition —
some subset of $U \oplus \mathrm{Bool}$ has the same total weight as its complement —
the original instance $(w, T)$ is a yes-instance of Subset Sum, i.e.\ some subset of $U$
has total weight exactly $T$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {U : Type*} [Fintype U] [DecidableEq U] in
/-- Soundness of reduction from Subset Sum to Partition. Note the hypothesis `(h : T ≤ ∑ a, w a)`. Because Lean's natural numbers `ℕ` do not support negative numbers (subtraction truncates at 0), we must assert that the target `T` is not strictly greater than the total weight of all items. (If it were, the Subset Sum would be trivially false anyway). -/
theorem SubsetSumToPartition.SubsetSumToPartitionSoundness (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a):
  Partition (partitionWeight w T) → SubsetSum w T := by
  classical
  rintro ⟨S', hS'⟩
  set S : Finset U := Finset.univ.filter (fun a => Sum.inl a ∈ S') with hSdef
  have hmemS : ∀ a : U, a ∈ S ↔ Sum.inl a ∈ S' := by
    intro a
    simp [hSdef]
  have keySplit : ∀ (t : Finset (U ⊕ Bool)) (Sf : Finset U),
      (∀ a, a ∈ Sf ↔ Sum.inl a ∈ t) →
      ∑ b ∈ t, partitionWeight w T b
        = (∑ a ∈ Sf, w a)
          + (if Sum.inr true ∈ t then partitionWeight w T (Sum.inr true) else 0)
          + (if Sum.inr false ∈ t then partitionWeight w T (Sum.inr false) else 0) := by
    intro t Sf hmem
    have hA : ∑ a : U, (if Sum.inl a ∈ t then partitionWeight w T (Sum.inl a) else 0)
        = ∑ a ∈ Sf, w a := by
      rw [← Fintype.sum_ite_mem Sf w]
      apply Finset.sum_congr rfl
      intro a _
      simp only [← hmem a, partitionWeight]
    rw [← Fintype.sum_ite_mem t (partitionWeight w T), Fintype.sum_sum_type, Fintype.sum_bool, hA]
    omega
  have hSplitS' := keySplit S' S hmemS
  have hSplitComp := keySplit S'ᶜ Sᶜ (fun a => by simp [Finset.mem_compl, hmemS a])
  have hSAcompl : (∑ a ∈ S, w a) + (∑ a ∈ Sᶜ, w a) = ∑ a, w a :=
    Finset.sum_add_sum_compl S w
  by_cases h1 : Sum.inr true ∈ S'
  · by_cases h2 : Sum.inr false ∈ S'
    · -- both dummies present: forces W = 0, so S works vacuously
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
    · -- only ⊤ present: S is the Subset Sum witness
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
  · by_cases h2 : Sum.inr false ∈ S'
    · -- only ⊥ present: the complement Sᶜ is the Subset Sum witness
      refine ⟨Sᶜ, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
    · -- neither dummy present: forces W = 0, so S works vacuously
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
