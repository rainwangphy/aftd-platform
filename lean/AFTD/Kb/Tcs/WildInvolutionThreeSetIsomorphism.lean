import AFTD.Prelude
import AFTD.Kb.Tcs.WildThreePartialInvolutionClassification
import AFTD.Kb.Tcs.WildInvolutionPartialPatternIsomorphismExtends

/-!
# wild_involution_three_set_isomorphism

Topic: graphs   Node: c284cb06564b

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

For two finite involutions with unique fixed points, two three-element subsets can be carried to one another by a global intertwining permutation if they agree on containing the fixed point and on containing a non-loop matching edge.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

theorem wild_involution_three_set_isomorphism
    {V : Type*} [Fintype V] [DecidableEq V]
    (f g : Equiv.Perm V) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (a b : V) (hfa : ∀ x, f x = x ↔ x = a) (hgb : ∀ x, g x = x ↔ x = b)
    (S T : Finset V) (hS : S.card = 3) (hT : T.card = 3)
    (hfixed : a ∈ S ↔ b ∈ T)
    (hedge : (∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x = y) ↔
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ g x = y) :
    ∃ e : Equiv.Perm V, (∀ x, e (f x) = g (e x)) ∧ S.image e = T := by
  classical
  let eS : S ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hS)
  let eT : T ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hT)
  let v : Fin 3 → V := fun j => (eS.symm j).val
  let w : Fin 3 → V := fun j => (eT.symm j).val
  have hv : Function.Injective v := by
    intro j k h; exact eS.symm.injective (Subtype.ext h)
  have hw : Function.Injective w := by
    intro j k h; exact eT.symm.injective (Subtype.ext h)
  have hvS : ∀ j, v j ∈ S := fun j => (eS.symm j).property
  have hwT : ∀ j, w j ∈ T := fun j => (eT.symm j).property
  have hSv : ∀ x ∈ S, ∃ j, v j = x := by
    intro x hx; exact ⟨eS ⟨x,hx⟩,congrArg Subtype.val (eS.symm_apply_apply _)⟩
  have hTw : ∀ x ∈ T, ∃ j, w j = x := by
    intro x hx; exact ⟨eT ⟨x,hx⟩,congrArg Subtype.val (eT.symm_apply_apply _)⟩
  let enc (h : V → V) (u : Fin 3 → V) (j : Fin 3) : Option (Fin 3) :=
    if hh : ∃ k, h (u j) = u k then some hh.choose else none
  have henc (h : V → V) (u : Fin 3 → V) (hu : Function.Injective u) (j k : Fin 3) :
      enc h u j = some k ↔ h (u j) = u k := by
    dsimp only [enc]
    split_ifs with hh
    · simp only [Option.some.injEq]
      constructor
      · intro he; exact he ▸ hh.choose_spec
      · intro he; apply hu; exact hh.choose_spec.symm.trans he
    · constructor
      · intro he; cases he
      · intro he; exact (hh ⟨k,he⟩).elim
  have hsym (h : Equiv.Perm V) (hh : Function.Involutive h)
      (u : Fin 3 → V) (hu : Function.Injective u) :
      ∀ j k, enc h u j = some k ↔ enc h u k = some j := by
    intro j k
    rw [henc h u hu,henc h u hu]
    constructor
    · intro he; rw [← he,hh]
    · intro he; rw [← he,hh]
  have huniq (h : Equiv.Perm V) (c : V) (hc : ∀ x, h x = x ↔ x = c)
      (u : Fin 3 → V) (hu : Function.Injective u) :
      ∀ j k, enc h u j = some j → enc h u k = some k → j = k := by
    intro j k hj hk
    apply hu
    exact ((hc _).mp ((henc h u hu j j).mp hj)).trans
      ((hc _).mp ((henc h u hu k k).mp hk)).symm
  have hfixv : (∃ j, enc f v j = some j) ↔ a ∈ S := by
    constructor
    · rintro ⟨j,hj⟩
      have he := (hfa _).mp ((henc f v hv j j).mp hj)
      exact he ▸ hvS j
    · intro ha
      obtain ⟨j,hj⟩ := hSv a ha
      exact ⟨j,(henc f v hv j j).mpr ((hfa _).mpr hj)⟩
  have hfixw : (∃ j, enc g w j = some j) ↔ b ∈ T := by
    constructor
    · rintro ⟨j,hj⟩
      have he := (hgb _).mp ((henc g w hw j j).mp hj)
      exact he ▸ hwT j
    · intro hb
      obtain ⟨j,hj⟩ := hTw b hb
      exact ⟨j,(henc g w hw j j).mpr ((hgb _).mpr hj)⟩
  have hedgev : (∃ j k, j ≠ k ∧ enc f v j = some k) ↔
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x = y := by
    constructor
    · rintro ⟨j,k,hjk,hjk'⟩
      exact ⟨v j,hvS j,v k,hvS k,fun h => hjk (hv h),(henc f v hv j k).mp hjk'⟩
    · rintro ⟨x,hx,y,hy,hxy,hfxy⟩
      obtain ⟨j,rfl⟩ := hSv x hx
      obtain ⟨k,rfl⟩ := hSv y hy
      exact ⟨j,k,fun h => hxy (congrArg v h),(henc f v hv j k).mpr hfxy⟩
  have hedgew : (∃ j k, j ≠ k ∧ enc g w j = some k) ↔
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ g x = y := by
    constructor
    · rintro ⟨j,k,hjk,hjk'⟩
      exact ⟨w j,hwT j,w k,hwT k,fun h => hjk (hw h),(henc g w hw j k).mp hjk'⟩
    · rintro ⟨x,hx,y,hy,hxy,hgxy⟩
      obtain ⟨j,rfl⟩ := hTw x hx
      obtain ⟨k,rfl⟩ := hTw y hy
      exact ⟨j,k,fun h => hxy (congrArg w h),(henc g w hw j k).mpr hgxy⟩
  obtain ⟨r,hr,hrp⟩ := wild_three_partial_involution_classification (enc f v) (enc g w)
    (hsym f hf v hv) (hsym g hg w hw) (huniq f a hfa v hv) (huniq g b hgb w hw)
    (hfixv.trans (hfixed.trans hfixw.symm)) (hedgev.trans (hedge.trans hedgew.symm))
  have hp : ∀ j k, f (v j) = v k ↔ g (w (r j)) = w (r k) := by
    intro j k
    exact (henc f v hv j k).symm.trans ((hrp j k).trans (henc g w hw (r j) (r k)))
  obtain ⟨e,he,hev⟩ := wild_involution_partial_pattern_isomorphism_extends
    f g hf hg a b hfa hgb v (w ∘ r) hv (hw.comp hr.1) hp
  refine ⟨e,he,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨j,rfl⟩ := hSv y hy
    rw [hev]
    exact hwT (r j)
  · intro hx
    obtain ⟨k,rfl⟩ := hTw x hx
    obtain ⟨j,rfl⟩ := hr.2 k
    exact mem_image.mpr ⟨v j,hvS j,hev j⟩
