import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# zero_forcing_root_exposed_unique_neighbor

Topic: graphs   Node: 6d9461ed3013

Provenance: helper lemma. A fort-union observation for the rooted recurrence towards OP-1399, arXiv:2611.11352.

If W is fort-free and contains a root-exposed fort, there is exactly one root neighbor belonging to any root-exposed fort contained in W.
-/

open SimpleGraph

section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

private def near_fort (r : V) (F : Finset V) : Prop :=
  r ∉ F ∧ ∀ u : V, u ≠ r → u ∉ F → ∀ w : V, w ∈ F → G.Adj u w →
    ∃ x : V, x ∈ F ∧ G.Adj u x ∧ x ≠ w

private theorem fort_blocks (S F : Set V)
    (hdisjoint : ∀ v, v ∈ F → v ∉ S)
    (hfort : ∀ u, u ∉ F → ∀ w, w ∈ F → G.Adj u w →
      ∃ x, x ∈ F ∧ G.Adj u x ∧ x ≠ w) :
    ∀ v, ZeroForced G S v → v ∉ F := by
  intro v hv
  induction hv with
  | init v hvS =>
    intro hvF
    exact hdisjoint v hvF hvS
  | step u w hu huw hothers ihu ihothers =>
    intro hwF
    obtain ⟨x, hxF, hux, hxw⟩ := hfort u ihu w hwF huw
    exact ihothers x hux hxw hxF

private theorem unique_exposed_neighbor (r : V) (W F H : Finset V)
    (hW : is_zero_forcing_set G ((Finset.univ \ W : Finset V) : Set V))
    (hFW : F ⊆ W) (hHW : H ⊆ W) (hF : near_fort G r F) (hH : near_fort G r H)
    (x y : V) (hx : x ∈ F) (hy : y ∈ H) (hrx : G.Adj r x) (hry : G.Adj r y) :
    x = y := by
  classical
  by_contra hxy
  let K : Finset V := F ∪ H
  have hKW : K ⊆ W := Finset.union_subset hFW hHW
  have hdisjoint : ∀ z, z ∈ (K : Set V) →
      z ∉ ((Finset.univ \ W : Finset V) : Set V) := by
    intro z hzK hzS
    exact (Finset.mem_sdiff.mp hzS).2 (hKW hzK)
  have hfort : ∀ u, u ∉ (K : Set V) → ∀ w, w ∈ (K : Set V) → G.Adj u w →
      ∃ z, z ∈ (K : Set V) ∧ G.Adj u z ∧ z ≠ w := by
    intro u hu w hw huw
    by_cases hur : u = r
    · subst u
      by_cases hwx : w = x
      · subst w
        exact ⟨y, Finset.mem_union_right F hy, hry, Ne.symm hxy⟩
      · exact ⟨x, Finset.mem_union_left H hx, hrx, Ne.symm hwx⟩
    · have huF : u ∉ F := by
        intro huF
        exact hu (Finset.mem_union_left H huF)
      have huH : u ∉ H := by
        intro huH
        exact hu (Finset.mem_union_right F huH)
      rcases Finset.mem_union.mp hw with hwF | hwH
      · obtain ⟨z, hz, huz, hzw⟩ := hF.2 u hur huF w hwF huw
        exact ⟨z, Finset.mem_union_left H hz, huz, hzw⟩
      · obtain ⟨z, hz, huz, hzw⟩ := hH.2 u hur huH w hwH huw
        exact ⟨z, Finset.mem_union_right F hz, huz, hzw⟩
  exact (fort_blocks G ((Finset.univ \ W : Finset V) : Set V) (K : Set V)
    hdisjoint hfort x (hW x)) (Finset.mem_union_left H hx)
end

theorem zero_forcing_root_exposed_unique_neighbor {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V)
    (W : Finset V)
    (hW : is_zero_forcing_set G ((Finset.univ \ W : Finset V) : Set V))
    (hE : zero_forcing_root_exposed_fort G r W) :
    ∃! v : V, G.Adj r v ∧ ∃ F : Finset V, F ⊆ W ∧ r ∉ F ∧ v ∈ F ∧
      ∀ u : V, u ≠ r → u ∉ F → ∀ w : V, w ∈ F → G.Adj u w →
        ∃ x : V, x ∈ F ∧ G.Adj u x ∧ x ≠ w := by
  obtain ⟨F, hFW, hrF, ⟨x, hx, hrx⟩, hnear⟩ := hE
  refine ⟨x, ⟨hrx, F, hFW, hrF, hx, hnear⟩, ?_⟩
  rintro y ⟨hry, H, hHW, hrH, hy, hHnear⟩
  exact (unique_exposed_neighbor G r W F H hW hFW hHW ⟨hrF, hnear⟩
    ⟨hrH, hHnear⟩ x y hx hy hrx hry).symm
