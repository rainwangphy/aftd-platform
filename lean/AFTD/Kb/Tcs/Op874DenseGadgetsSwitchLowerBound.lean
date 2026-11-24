import AFTD.Prelude
import AFTD.Kb.Tcs.StrongTruncationMissingColorEdgeBound
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_dense_gadgets_switch_lower_bound

Topic: graphs   Node: 7980bfd64d7a

Provenance: helper lemma. OP-874: dense gadget obstruction to bounded component-switch repair, experiments 38459 and 38467.

If m dense vertex sets must each acquire two colors that are initially absent, and each recoloring step adds at most one such set-color occurrence, then a strong completion requires at least 2m steps.
-/

private theorem op874ds_progress_card_le {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (n : ℕ) (h0 : S 0 = ∅)
    (hstep : ∀ i < n, ((S (i+1)) \ (S i)).card ≤ 1) :
    (S n).card ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hi : (S n).card ≤ n := ih (fun i hi => hstep i (by omega))
    have hs := hstep n (by omega)
    have hc := Finset.card_le_card_sdiff_add_card (s := S (n+1)) (t := S n)
    omega

private theorem op874ds_two_targets
    (m n : ℕ) (S : ℕ → Finset (Fin m × Fin 2))
    (h0 : S 0 = ∅)
    (hstep : ∀ i < n, ((S (i+1)) \ (S i)).card ≤ 1)
    (hfinal : S n = Finset.univ) : 2*m ≤ n := by
  have h := op874ds_progress_card_le S n h0 hstep
  rw [hfinal] at h
  simpa [Fintype.card_prod, Nat.mul_comm] using h


private theorem op874ds_dense_sees_color
    {V E Ω : Type*} [DecidableEq V] [Fintype E] [Fintype Ω]
    (hΩ : Fintype.card Ω = 6) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (a : Ω) (S : Finset V)
    (hdense : S.card < (Finset.univ.filter fun e : E =>
      ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v)).card) :
    ∃ v ∈ S, ∃ e, v ∈ ends e ∧ c v e = a := by
  classical
  by_contra hn
  have hS : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a := by
    intro v hv e he heq
    exact hn ⟨v,hv,e,he,heq⟩
  have bound := strong_truncation_missing_color_edge_bound
    hΩ ends hloop hcubic c h hc hh hch hs a S hS
  apply (Nat.not_lt_of_ge bound)
  convert hdense using 1 <;> congr 1 <;> ext x <;> simp

theorem op874_dense_gadgets_switch_lower_bound
    {V E : Type*} [DecidableEq V] [Fintype E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (m n : ℕ) (S : Fin m → Finset V) (c : ℕ → V → E → Fin 6)
    (h : V → E → Fin 6) (seen : ℕ → Finset (Fin m × Fin 2))
    (hseen : ∀ t i j, (i,j) ∈ seen t ↔
      ∃ v ∈ S i, ∃ e, v ∈ ends e ∧ c t v e = (if j = 0 then 2 else 5))
    (h0 : seen 0 = ∅)
    (hstep : ∀ t < n, ((seen (t+1)) \ (seen t)).card ≤ 1)
    (hdense : ∀ i, (S i).card < (Finset.univ.filter fun e : E =>
      ∃ u ∈ S i, ∃ v ∈ S i, ends e = s(u,v)).card)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c n v e = c n v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c n v f)
    (hs : truncation_local_states_define_strong_coloring ends (c n) h) :
    2*m ≤ n := by
  classical
  apply op874ds_two_targets m n seen h0 hstep
  apply Finset.eq_univ_iff_forall.mpr
  rintro ⟨i,j⟩
  apply (hseen n i j).2
  exact op874ds_dense_sees_color
    (by decide : Fintype.card (Fin 6)=6) ends hloop hcubic (c n) h hc hh hch hs
    (if j=0 then 2 else 5) (S i) (hdense i)
