import AFTD.Prelude
import AFTD.Kb.Tcs.IsTokenSegmentation

/-!
# is_token_segmentation_singleton

Topic: approximation   Node: f3f8dfccc76b

Provenance: helper lemma. arXiv:2611.15074, Section 2.1

Every word y admits a valid token segmentation into singletons over any vocabulary V.
-/

/-- Sanity lemma: partitioning into singletons is a valid token segmentation. -/
theorem is_token_segmentation_singleton {α : Type*} (V : Set (List α)) (y : List α) :
    is_token_segmentation V y (y.map (fun c => [c])) := by
  unfold is_token_segmentation
  constructor
  · induction y with
    | nil => rfl
    | cons a t ih => simp [ih]
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨c, _, rfl⟩ := ht
    right
    simp
