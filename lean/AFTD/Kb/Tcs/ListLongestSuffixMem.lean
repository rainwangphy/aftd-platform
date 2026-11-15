import AFTD.Prelude

/-!
# list_longest_suffix_mem

Topic: automata   Node: d7d025013d00

Provenance: helper lemma. step towards op_1716_sequential_subset_sync_sharp_k_approximation

For a finite set B of words containing the empty word and any word u, the longest element of B that is a suffix of u.
-/

/-- The longest member of B that is a suffix of u, chosen noncomputably. -/
noncomputable def list_longest_suffix_mem {α : Type*} [DecidableEq α]
    (B : Finset (List α)) (h0 : ([] : List α) ∈ B) (u : List α) : List α := Classical.choose (p := fun s : List α =>
      s ∈ B ∧ s <:+ u ∧ ∀ t : List α, t ∈ B → t <:+ u → t.length ≤ s.length) (by
    have hne : (B.filter (fun t => t <:+ u)).Nonempty :=
      ⟨[], Finset.mem_filter.mpr ⟨h0, List.nil_suffix⟩⟩
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ (fun t : List α => t.length) hne
    obtain ⟨hsB, hsu⟩ := Finset.mem_filter.mp hs
    exact ⟨s, hsB, hsu, fun t ht htu => hmax t (Finset.mem_filter.mpr ⟨ht, htu⟩)⟩)
