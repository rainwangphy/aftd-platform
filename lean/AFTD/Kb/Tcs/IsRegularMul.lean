import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularIffEnfa

/-!
# is_regular_mul

Topic: automata   Node: d09e9ff8e891

The concatenation of two regular languages is regular.
-/

open Language Set

def is_regular_mul_f {α : Type*} (L2 : Language α) (p : Language α × Set (Language α)) : Language α :=
  ((p.1 * L2 : Set (List α)) ∪ (⋃₀ p.2 : Set (List α)) : Set (List α))

def is_regular_mul_S {α : Type*} (L1 L2 : Language α) (w : List α) : Set (Language α) :=
  { K | ∃ bs, (∃ u ∈ L1, u ++ bs = w) ∧ K = L2.leftQuotient bs }

lemma is_regular_mul_S_subset {α : Type*} (L1 L2 : Language α) (w : List α) :
    is_regular_mul_S L1 L2 w ⊆ range L2.leftQuotient := by
  rintro K ⟨bs, _, rfl⟩
  exact ⟨bs, rfl⟩

lemma is_regular_mul_leftQuotient_eq {α : Type*} (L1 L2 : Language α) (w : List α) :
    (L1 * L2).leftQuotient w = is_regular_mul_f L2 (L1.leftQuotient w, is_regular_mul_S L1 L2 w) := by
  ext y
  simp only [mem_leftQuotient, is_regular_mul_f, Language.mem_mul, is_regular_mul_S]
  constructor
  · intro hy
    rcases hy with ⟨u, hu, v, hv, huv⟩
    rw [List.append_eq_append_iff] at huv
    rcases huv with (⟨as, hu', hy'⟩ | ⟨bs, hw', hv'⟩)
    · right
      refine ⟨L2.leftQuotient as, ⟨as, ⟨u, hu, hu'.symm⟩, rfl⟩, ?_⟩
      show as ++ y ∈ L2
      rw [← hy']
      exact hv
    · left
      refine ⟨bs, ?_, v, hv, hv'.symm⟩
      show w ++ bs ∈ L1
      rw [← hw']
      exact hu
  · rintro (⟨as, has, v, hv, rfl⟩ | ⟨K, ⟨bs, ⟨u, hu, rfl⟩, rfl⟩, hy⟩)
    · refine ⟨w ++ as, has, v, hv, by simp [List.append_assoc]⟩
    · refine ⟨u, hu, bs ++ y, hy, by simp [List.append_assoc]⟩

/-- Regular languages are closed under concatenation. -/
theorem is_regular_mul {α : Type*} {L1 L2 : Language α} (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient] at h1 h2 ⊢
  have H : (is_regular_mul_f L2 '' (Set.range L1.leftQuotient ×ˢ Set.powerset (Set.range L2.leftQuotient))).Finite :=
    (h1.prod h2.powerset).image (is_regular_mul_f L2)
  refine H.subset ?_
  rintro _ ⟨w, rfl⟩
  rw [is_regular_mul_leftQuotient_eq]
  exact Set.mem_image_of_mem _ ⟨Set.mem_range_self w, is_regular_mul_S_subset L1 L2 w⟩
