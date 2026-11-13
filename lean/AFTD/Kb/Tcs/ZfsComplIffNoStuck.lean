import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zfs_compl_iff_no_stuck

Topic: graphs   Node: 81fdb0deba26

Provenance: helper lemma. step towards gt_zero_forcing_poly_not_unimodal

For any finite graph G and finite T, the complement V\T is a zero forcing set precisely when T contains no nonempty "stuck" subset W, i.e. no nonempty W ⊆ T such that every vertex outside W is adjacent to at most one vertex of W (or to any given w it never sees w as its unique W-neighbour).
-/

open SimpleGraph

private theorem zf_fort_blocking_induct {V : Type*} (G : SimpleGraph V) (S F : Set V)
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

theorem zfs_compl_iff_no_stuck {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V) :
    is_zero_forcing_set G ((Finset.univ \ T : Finset V) : Set V) ↔
    ¬ ∃ W : Finset V, W.Nonempty ∧ W ⊆ T ∧
        (∀ u : V, u ∉ W → ∀ w : V, w ∈ W → G.Adj u w → ∃ x : V, x ∈ W ∧ G.Adj u x ∧ x ≠ w) := by
  classical
  let S : Set V := ((Finset.univ \ T : Finset V) : Set V)
  change is_zero_forcing_set G S ↔ _
  constructor
  · intro h ⟨W, ⟨v, hv⟩, hWT, hfort⟩
    have hd : ∀ x, x ∈ (W : Set V) → x ∉ S := by
      intro x hxW hxS
      exact (Finset.mem_sdiff.mp hxS).2 (hWT hxW)
    exact zf_fort_blocking_induct G S (W : Set V) hd hfort v (h v) hv
  · intro h v
    by_contra hv
    let W : Finset V := Finset.univ.filter (fun x => ¬ ZeroForced G S x)
    have hW : W.Nonempty := ⟨v, by simp [W, hv]⟩
    have hWT : W ⊆ T := by
      intro x hx
      have hnx : ¬ ZeroForced G S x := (Finset.mem_filter.mp hx).2
      by_contra hxT
      apply hnx
      exact ZeroForced.init x (by simp [S, hxT])
    have hfort : ∀ u : V, u ∉ W → ∀ w : V, w ∈ W → G.Adj u w →
        ∃ x : V, x ∈ W ∧ G.Adj u x ∧ x ≠ w := by
      intro u hu w hw huw
      have huS : ZeroForced G S u := by
        by_contra hnu
        apply hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hnu⟩
      by_contra hn
      have hall : ∀ x, G.Adj u x → x ≠ w → ZeroForced G S x := by
        intro x hux hxw
        by_contra hnx
        apply hn
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hnx⟩, hux, hxw⟩
      exact (Finset.mem_filter.mp hw).2 (ZeroForced.step u w huS huw hall)
    exact h ⟨W, hW, hWT, hfort⟩
