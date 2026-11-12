import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser

/-!
# op_193_covering_color_obstruction

Topic: graphs   Node: f3fbe2336d12

Provenance: helper lemma. The final coloring obstruction in arXiv:2610.17884 Theorem 1.4.

If every proper q-coloring of the cycle-stable k-set graph has a stable (k-1)-set whose disjoint stable k-sets realize all q colors, then the stable k-set graph of the cycle plus an isolated vertex is not q-colorable.
-/

namespace Inbox777Bridge
variable (m k q : ℕ)

def lift (U : {S : Finset (Fin m) // (SimpleGraph.cycleGraph m).IsNIndepSet k S}) :
    {T : Finset (Fin m ⊕ Unit) // ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k T} :=
  ⟨U.1.map Function.Embedding.inl, by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_map]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
      dsimp [SimpleGraph.sum]
      intro h
      exact U.2.isIndepSet hu hv (by simpa using hne) h
    · simpa using U.2.card_eq⟩

def extra (hk : 1 ≤ k) (F : Finset (Fin m)) (hc : F.card = k-1)
    (hi : (SimpleGraph.cycleGraph m).IsIndepSet (↑F : Set (Fin m))) :
    {T : Finset (Fin m ⊕ Unit) // ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k T} :=
  ⟨insert (Sum.inr ()) (F.map Function.Embedding.inl), by
    refine ⟨?_, ?_⟩
    · intro x hx y hy hne hadj
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hx' : x ∈ F := by simpa using hx
          have hy' : y ∈ F := by simpa using hy
          exact hi hx' hy' (by simpa using hne) hadj
        | inr y => cases hadj
      | inr x =>
        cases y with
        | inl y => cases hadj
        | inr y => cases x; cases y; exact hne rfl
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_map, hc]; omega
      · simp⟩


end Inbox777Bridge
open Inbox777Bridge

theorem op_193_covering_color_obstruction (m k q : ℕ) (hk : 1 ≤ k)
    (hcover : ∀ c : {S : Finset (Fin m) // (SimpleGraph.cycleGraph m).IsNIndepSet k S} → Fin q,
      (∀ U W, Disjoint U.1 W.1 → c U ≠ c W) →
      ∃ F : Finset (Fin m), F.card = k-1 ∧ (SimpleGraph.cycleGraph m).IsIndepSet (↑F : Set (Fin m)) ∧
        ∀ i : Fin q, ∃ U, c U = i ∧ Disjoint F U.1) :
    ¬ (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).Colorable q := by
  rintro ⟨C⟩
  let c : {S : Finset (Fin m) // (SimpleGraph.cycleGraph m).IsNIndepSet k S} → Fin q := fun U => C (lift m k U)
  have hp : ∀ U W, Disjoint U.1 W.1 → c U ≠ c W := by
    intro U W hd
    apply C.valid
    refine ⟨(Finset.disjoint_map Function.Embedding.inl).mpr hd, ?_⟩
    intro h
    have heq : U.1 = W.1 := Finset.map_injective Function.Embedding.inl (congrArg Subtype.val h)
    have hp : U.1.Nonempty := Finset.card_pos.mp (by rw [U.2.card_eq]; omega)
    obtain ⟨x, hx⟩ := hp
    exact (Finset.disjoint_left.mp hd) hx (by rw [← heq]; exact hx)
  obtain ⟨F, hc, hi, hcolors⟩ := hcover c hp
  let V := extra m k hk F hc hi
  obtain ⟨U, heq, hd⟩ := hcolors (C V)
  have he : (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).Adj V (lift m k U) := by
    refine ⟨?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      have hmapped : Disjoint (F.map (Function.Embedding.inl : Fin m ↪ Fin m ⊕ Unit))
          (U.1.map (Function.Embedding.inl : Fin m ↪ Fin m ⊕ Unit)) :=
        (Finset.disjoint_map (Function.Embedding.inl : Fin m ↪ Fin m ⊕ Unit)).mpr hd
      simp only [V, extra, Finset.mem_insert] at hx
      rcases hx with hx | hx
      · subst x; simp [lift] at hy
      · exact (Finset.disjoint_left.mp hmapped) hx hy
    · intro heq'
      have hmem : (Sum.inr () : Fin m ⊕ Unit) ∈ V.1 := by simp [V, extra]
      rw [congrArg Subtype.val heq'] at hmem
      simp [lift] at hmem
  exact C.valid he (by simpa [c] using heq.symm)
