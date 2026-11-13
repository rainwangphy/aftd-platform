import AFTD.Prelude
import AFTD.Kb.Tcs.Op1525InvariantMonoSubsetReconstruct
import AFTD.Kb.Tcs.SignedGraphIsBalancedPartition
import AFTD.Kb.Tcs.SignedGraphIsReconstructible
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraphSameDeck
import AFTD.Kb.Tcs.SignedGraphSwitch
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# signed_graph_reconstructible_balanced_mono_invariant

Topic: combinatorics   Node: baa17aa684f5

Provenance: original. Related work: A structural subcase of OP-1525, suggested by the bipartition model in arXiv:2611.13901, Section 4.1.

A connected balanced signed graph is reconstructible from its switching deck if its underlying graph has an automorphism-invariant vertex set of at least three vertices that lies entirely in one part of a balance partition, with at least two vertices outside the set.
-/

namespace OP1525MonoPoly
variable {V : Type*} [DecidableEq V]

def flip (f : V → Bool) (v x : V) : Bool := xor (f x) (decide (x = v))
def mono (S : Set V) (f : V → Bool) : Prop := ∀ x ∈ S, ∀ y ∈ S, f x = f y

lemma xor_cancel_common (x y c : Bool) : xor x c = xor y c → x = y := by
  cases x <;> cases y <;> cases c <;> decide
lemma xor_cancel_flip (a b c d : Bool) : xor a d = xor (xor b d) c → a = xor b c := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma fresh_of_three (S : Set V) (a b c : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u v : V) :
    ∃ z ∈ S, z ≠ u ∧ z ≠ v := by
  by_cases h : a ≠ u ∧ a ≠ v
  · exact ⟨a, ha, h⟩
  by_cases h' : b ≠ u ∧ b ≠ v
  · exact ⟨b, hb, h'⟩
  by_cases h'' : c ≠ u ∧ c ≠ v
  · exact ⟨c, hc, h''⟩
  exfalso
  push_neg at h h' h''
  have ha' : a = u ∨ a = v := by by_cases ht : a = u <;> aesop
  have hb' : b = u ∨ b = v := by by_cases ht : b = u <;> aesop
  have hc' : c = u ∨ c = v := by by_cases ht : c = u <;> aesop
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
    rcases hc' with hc' | hc' <;> subst_vars <;> contradiction

lemma mono_of_two_flips (S : Set V) (f : V → Bool) (u v : V) (huv : u ≠ v)
    (hthree : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h1 : mono S (flip f u)) (h2 : mono S (flip f v)) : mono S f := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hthree
  obtain ⟨z, hz, hzu, hzv⟩ := fresh_of_three S a b c ha hb hc hab hac hbc u v
  have heq (x : V) (hx : x ∈ S) : f x = f z := by
    by_cases hxu : x = u
    · have hxv : x ≠ v := by simpa [hxu] using huv
      have hh := h2 x hx z hz
      simpa [mono, flip, hxv, hzv] using hh
    · have hh := h1 x hx z hz
      simpa [mono, flip, hxu, hzu] using hh
  intro x hx y hy
  exact (heq x hx).trans (heq y hy).symm

lemma flip_outside_mono (S : Set V) (f : V → Bool) (v : V)
    (hf : mono S f) (hv : v ∉ S) : mono S (flip f v) := by
  intro x hx y hy
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hyv : y ≠ v := fun h => hv (h ▸ hy)
  simpa [flip, hxv, hyv] using hf x hx y hy

lemma transfer_mono (S : Set V) (F H : V → Bool) (g : Equiv.Perm V) (c : Bool)
    (hpres : ∀ x, x ∈ S ↔ g x ∈ S)
    (heq : ∀ x, F (g x) = xor (H x) c) (hF : mono S F) : mono S H := by
  intro x hx y hy
  apply xor_cancel_common _ _ c
  rw [← heq x, ← heq y]
  exact hF (g x) ((hpres x).mp hx) (g y) ((hpres y).mp hy)

theorem reconstruct_of_invariant_monochrome
    (A B : V → Bool) (P : Equiv.Perm V → Prop) (S : Set V)
    (a b c : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (u v : V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hA : ∀ x ∈ S, ∀ y ∈ S, A x = A y)
    (hpres : ∀ g, P g → ∀ x, x ∈ S ↔ g x ∈ S)
    (π : Equiv.Perm V)
    (hdeck : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (A (g x)) (decide (g x = w)) =
        xor (xor (B x) (decide (x = π w))) d) :
    ∃ g, P g ∧ ∃ d : Bool, ∀ x, A (g x) = xor (B x) d := by
  have hthree : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  obtain ⟨g1, hg1, d1, heq1⟩ := hdeck u
  obtain ⟨g2, hg2, d2, heq2⟩ := hdeck v
  have hB1 : mono S (flip B (π u)) :=
    transfer_mono S _ _ g1 d1 (hpres g1 hg1) heq1 (flip_outside_mono S A u hA hu)
  have hB2 : mono S (flip B (π v)) :=
    transfer_mono S _ _ g2 d2 (hpres g2 hg2) heq2 (flip_outside_mono S A v hA hv)
  have hB : mono S B := mono_of_two_flips S B (π u) (π v) (fun h => huv (π.injective h)) hthree hB1 hB2
  obtain ⟨g, hg, d, heq⟩ := hdeck a
  let q := g.symm a
  have hgq : g q = a := by simp [q]
  have hq : q ∈ S := by
    apply (hpres g hg q).mpr
    simpa [hgq] using ha
  have hmatch : q = π a := by
    by_contra hne
    obtain ⟨z, hz, hzq, hzw⟩ := fresh_of_three S a b c ha hb hc hab hac hbc q (π a)
    have hgzS : g z ∈ S := (hpres g hg z).mp hz
    have hgz : g z ≠ a := by
      intro he
      apply hzq
      apply g.injective
      simpa [hgq] using he
    have hAz : A (g z) = A a := hA (g z) hgzS a ha
    have hBqz : B q = B z := hB q hq z hz
    have hqeq := heq q
    have hzeq := heq z
    simp [flip, hgq, hne, hBqz] at hqeq
    simp [flip, hgz, hzw, hAz] at hzeq
    cases hAa : A a <;> cases hBz : B z <;> cases hd : d <;>
      simp [hAa, hBz, hd] at hqeq hzeq
  refine ⟨g, hg, d, ?_⟩
  intro x
  have hEq := heq x
  have hpred : (g x = a) ↔ x = π a := by
    constructor
    · intro h
      have hsame : g x = g q := h.trans hgq.symm
      exact (g.injective hsame).trans hmatch
    · intro h
      subst x
      simpa [hmatch] using hgq
  have hdec : decide (g x = a) = decide (x = π a) := by
    simp only [hpred]
  rw [hdec] at hEq
  exact xor_cancel_flip _ _ _ _ hEq

end OP1525MonoPoly


namespace OP1525Bridge

lemma bool_xor_square (a b c d : Bool) : xor a b = xor c d → xor a c = xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma bool_xor_solve (a b c : Bool) : xor a b = c → a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

lemma connected_labels {V : Type*} (G : SimpleGraph V) (hc : G.Connected) (a b : V → Bool)
    (he : ∀ u v, G.Adj u v → xor (a u) (a v) = xor (b u) (b v)) :
    ∃ c : Bool, ∀ x, a x = xor (b x) c := by
  letI : Nonempty V := hc.nonempty
  let r : V := Classical.choice inferInstance
  have hedge (u v : V) (h : G.Adj u v) : xor (a u) (b u) = xor (a v) (b v) :=
    bool_xor_square _ _ _ _ (he u v h)
  have hpath : ∀ x, Relation.ReflTransGen G.Adj r x → xor (a r) (b r) = xor (a x) (b x) := by
    intro x p
    induction p with
    | refl => rfl
    | tail _ h ih => exact ih.trans (hedge _ _ h)
  refine ⟨xor (a r) (b r), ?_⟩
  intro x
  exact bool_xor_solve _ _ _ (hpath x ((SimpleGraph.reachable_iff_reflTransGen r x).mp (hc r x))).symm

def color {V : Type*} [DecidableEq V] (A : Finset V) (v : V) : Bool := decide (v ∈ A)
def sign (p : Bool) : ℤ := if p then -1 else 1

lemma balanced_sign {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B)
    (u v : V) (h : G.graph.Adj u v) :
    G.sgn ⟨s(u, v), h⟩ = sign (xor (color A u) (color A v)) := by
  have hB (x : V) (hx : x ∉ A) : x ∈ B := by
    have hall : x ∈ A ∪ B := by rw [hbal.1]; exact Finset.mem_univ x
    exact (Finset.mem_union.mp hall).resolve_left hx
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).1 (Or.inl ⟨hu, hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).2 (Or.inl ⟨hu, hB v hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).2 (Or.inr ⟨hB u hu, hv⟩)
  · simpa [sign, color, hu, hv] using (hbal.2.2 u v h).1 (Or.inr ⟨hB u hu, hB v hv⟩)


def flipped {V : Type*} [DecidableEq V] (f : V → Bool) (w x : V) : Bool :=
  xor (f x) (decide (x = w))

lemma sign_injective {a b : Bool} (h : sign a = sign b) : a = b := by
  cases a <;> cases b <;> simp [sign] at h ⊢

lemma switched_sign {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B) (w u v : V) (h : G.graph.Adj u v) :
    (G.switch w).sgn ⟨s(u, v), h⟩ =
      sign (xor (flipped (color A) w u) (flipped (color A) w v)) := by
  change (if w ∈ s(u, v) then -G.sgn ⟨s(u, v), h⟩ else G.sgn ⟨s(u, v), h⟩) = _
  rw [balanced_sign G A B hbal u v h]
  have hne : u ≠ v := G.graph.ne_of_adj h
  by_cases hu : u = w <;> by_cases hv : v = w
  · exact False.elim (hne (hu.trans hv.symm))
  · subst u
    cases h1 : color A w <;> cases h2 : color A v <;>
      simp [Sym2.mem_iff, hv, Ne.symm hv, sign, flipped, h1, h2]
  · subst v
    cases h1 : color A u <;> cases h2 : color A w <;>
      simp [Sym2.mem_iff, hu, Ne.symm hu, sign, flipped, h1, h2]
  · simp [Sym2.mem_iff, hu, hv, Ne.symm hu, Ne.symm hv, flipped]

end OP1525Bridge

namespace OP1525Bridge

lemma sign_flip_left (a b : Bool) : sign (xor (xor a true) b) = -sign (xor a b) := by
  cases a <;> cases b <;> decide
lemma sign_flip_right (a b : Bool) : sign (xor a (xor b true)) = -sign (xor a b) := by
  cases a <;> cases b <;> decide

lemma from_switched_iso {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype W]
    (H : SignedGraph W) (G : SimpleGraph V) (f : G ≃g H.graph) (w : W) (F : V → Bool)
    (hcard : ∀ u v (h : G.Adj u v),
      (H.switch w).sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ = sign (xor (F u) (F v))) :
    ∀ u v (h : G.Adj u v),
      H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ =
        sign (xor (flipped F (f.symm w) u) (flipped F (f.symm w) v)) := by
  intro u v h
  have hne : u ≠ v := G.ne_of_adj h
  have hm : w ∈ s(f u, f v) ↔ u = f.symm w ∨ v = f.symm w := by
    have hf (z : V) : w = f z ↔ z = f.symm w := by
      constructor
      · intro h
        apply f.injective
        simpa using h.symm
      · intro h
        subst z
        simp
    simp only [Sym2.mem_iff, hf]
  have hh := hcard u v h
  change (if w ∈ s(f u, f v) then -H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩
    else H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩) = _ at hh
  by_cases hu : u = f.symm w <;> by_cases hv : v = f.symm w
  · exact False.elim (hne (hu.trans hv.symm))
  · have hw : w ∈ s(f u, f v) := hm.mpr (Or.inl hu)
    simp [hw] at hh
    have hdu : decide (u = f.symm w) = true := by simp [hu]
    have hdv : decide (v = f.symm w) = false := by simp [hv]
    simp only [flipped, hdu, hdv, Bool.xor_false]
    rw [sign_flip_left]
    linarith
  · have hw : w ∈ s(f u, f v) := hm.mpr (Or.inr hv)
    simp [hw] at hh
    have hdu : decide (u = f.symm w) = false := by simp [hu]
    have hdv : decide (v = f.symm w) = true := by simp [hv]
    simp only [flipped, hdu, hdv, Bool.xor_false]
    rw [sign_flip_right]
    linarith
  · have hw : w ∉ s(f u, f v) := fun hh' => (hm.mp hh').elim hu hv
    simpa [hw, flipped, hu, hv] using hh

end OP1525Bridge

namespace OP1525Bridge

lemma to_switched_iso {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype W]
    (H : SignedGraph W) (G : SimpleGraph V) (f : G ≃g H.graph) (w : W) (F : V → Bool)
    (hrep : ∀ u v (h : G.Adj u v),
      H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ = sign (xor (F u) (F v))) :
    ∀ u v (h : G.Adj u v),
      (H.switch w).sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ =
        sign (xor (flipped F (f.symm w) u) (flipped F (f.symm w) v)) := by
  intro u v h
  have hne : u ≠ v := G.ne_of_adj h
  have hm : w ∈ s(f u, f v) ↔ u = f.symm w ∨ v = f.symm w := by
    have hf (z : V) : w = f z ↔ z = f.symm w := by
      constructor
      · intro hz
        apply f.injective
        simpa using hz.symm
      · intro hz
        subst z
        simp
    simp only [Sym2.mem_iff, hf]
  change (if w ∈ s(f u, f v) then -H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩
    else H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩) = _
  rw [hrep u v h]
  by_cases hu : u = f.symm w <;> by_cases hv : v = f.symm w
  · exact False.elim (hne (hu.trans hv.symm))
  · have hw : w ∈ s(f u, f v) := hm.mpr (Or.inl hu)
    have hdu : decide (u = f.symm w) = true := by simp [hu]
    have hdv : decide (v = f.symm w) = false := by simp [hv]
    simp only [hw, ↓reduceIte, flipped, hdu, hdv, Bool.xor_false]
    exact (sign_flip_left _ _).symm
  · have hw : w ∈ s(f u, f v) := hm.mpr (Or.inr hv)
    have hdu : decide (u = f.symm w) = false := by simp [hu]
    have hdv : decide (v = f.symm w) = true := by simp [hv]
    simp only [hw, ↓reduceIte, flipped, hdu, hdv, Bool.xor_false]
    exact (sign_flip_right _ _).symm
  · have hw : w ∉ s(f u, f v) := fun hh => (hm.mp hh).elim hu hv
    simp [hw, flipped, hu, hv]

end OP1525Bridge

namespace OP1525Bridge

lemma xor_common (a b c : Bool) : xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> decide

theorem deck_color_model {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
    (G : SignedGraph V) (H : SignedGraph W) (hconn : G.graph.Connected)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B) (π0 : V ≃ W)
    (hcards : ∀ v, (G.switch v).IsIsomorphic (H.switch (π0 v))) (a : V) :
    ∃ (F : V → Bool) (π : Equiv.Perm V),
      (∀ v, ∃ g : G.graph ≃g G.graph, ∃ c : Bool, ∀ x,
        flipped (color A) v (g x) = xor (flipped F (π v) x) c) ∧
      (∀ (g : G.graph ≃g G.graph) (c : Bool),
        (∀ x, color A (g x) = xor (F x) c) → G.IsIsomorphic H) := by
  classical
  obtain ⟨f, hf⟩ := hcards a
  let F0 : V → Bool := flipped (color A) a
  let F : V → Bool := flipped F0 (f.symm (π0 a))
  have hcard0 : ∀ u v (h : G.graph.Adj u v),
      (H.switch (π0 a)).sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ = sign (xor (F0 u) (F0 v)) := by
    intro u v h
    rw [hf u v h]
    exact switched_sign G A B hbal a u v h
  have hrep : ∀ u v (h : G.graph.Adj u v),
      H.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ = sign (xor (F u) (F v)) :=
    from_switched_iso H G.graph f (π0 a) F0 hcard0
  let π : Equiv.Perm V := π0.trans f.toEquiv.symm
  refine ⟨F, π, ?_, ?_⟩
  · intro v
    obtain ⟨fv, hfv⟩ := hcards v
    let g : G.graph ≃g G.graph := f.trans fv.symm
    have he : ∀ u w, G.graph.Adj u w →
        xor (flipped (color A) v (g u)) (flipped (color A) v (g w)) =
          xor (flipped F (π v) u) (flipped F (π v) w) := by
      intro u w h
      apply sign_injective
      calc
        sign (xor (flipped (color A) v (g u)) (flipped (color A) v (g w))) =
            (G.switch v).sgn ⟨s(g u, g w), g.map_adj_iff.mpr h⟩ :=
          (switched_sign G A B hbal v (g u) (g w) (g.map_adj_iff.mpr h)).symm
        _ = (H.switch (π0 v)).sgn ⟨s(f u, f w), f.map_adj_iff.mpr h⟩ := by
          have hp := (hfv (g u) (g w) (g.map_adj_iff.mpr h)).symm
          have hcomp (x : V) : fv (g x) = f x := by
            change fv (fv.symm (f x)) = f x
            exact fv.apply_symm_apply _
          simpa only [hcomp] using hp
        _ = sign (xor (flipped F (π v) u) (flipped F (π v) w)) := by
          have hp : π v = f.symm (π0 v) := rfl
          rw [hp]
          exact to_switched_iso H G.graph f (π0 v) F hrep u w h
    obtain ⟨c, hc⟩ := connected_labels G.graph hconn (fun x => flipped (color A) v (g x))
      (flipped F (π v)) he
    exact ⟨g, c, hc⟩
  · intro g c hc
    let z : G.graph ≃g H.graph := g.symm.trans f
    refine ⟨z, ?_⟩
    intro u v h
    have hu : color A u = xor (F (g.symm u)) c := by simpa using hc (g.symm u)
    have hv : color A v = xor (F (g.symm v)) c := by simpa using hc (g.symm v)
    calc
      H.sgn ⟨s(z u, z v), z.map_adj_iff.mpr h⟩ =
          sign (xor (F (g.symm u)) (F (g.symm v))) := by
        change H.sgn ⟨s(f (g.symm u), f (g.symm v)), _⟩ = _
        exact hrep (g.symm u) (g.symm v) (g.symm.map_adj_iff.mpr h)
      _ = sign (xor (color A u) (color A v)) := by rw [hu, hv, xor_common]
      _ = G.sgn ⟨s(u, v), h⟩ := (balanced_sign G A B hbal u v h).symm

end OP1525Bridge

namespace OP1525Bridge

end OP1525Bridge

open OP1525Bridge

theorem signed_graph_reconstructible_balanced_mono_invariant {V : Type*}
    [DecidableEq V] [Fintype V] (G : SignedGraph V) (hconn : G.graph.Connected)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B) (S : Finset V)
    (hbig : S.card ≥ 3) (hout : (Finset.univ \ S).card ≥ 2)
    (hmono : S ⊆ A ∨ S ⊆ B)
    (hinvariant : ∀ f : G.graph ≃g G.graph, ∀ x, x ∈ S ↔ f x ∈ S) :
    G.IsReconstructible := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp (show 2 < S.card by omega)
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Finset.one_lt_card.mp (show 1 < (Finset.univ \ S).card by omega)
  have huS : u ∉ S := (Finset.mem_sdiff.mp hu).2
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hA : ∀ (x : V), x ∈ S → ∀ (y : V), y ∈ S → OP1525Bridge.color A x = OP1525Bridge.color A y := by
    rcases hmono with h | h
    · intro x hx y hy
      simp [OP1525Bridge.color, h hx, h hy]
    · intro x hx y hy
      have hnotx : x ∉ A := fun hxA => (Finset.disjoint_left.mp hbal.2.1) hxA (h hx)
      have hnoty : y ∉ A := fun hyA => (Finset.disjoint_left.mp hbal.2.1) hyA (h hy)
      simp [OP1525Bridge.color, hnotx, hnoty]
  unfold SignedGraph.IsReconstructible
  intro W _ _ H hdeck
  obtain ⟨π0, hcards⟩ := hdeck
  obtain ⟨F, π, hcolors, hlift⟩ := deck_color_model G H hconn A B hbal π0 hcards a
  let P : Equiv.Perm V → Prop := fun p => ∃ g : G.graph ≃g G.graph, g.toEquiv = p
  have hpres : ∀ p, P p → ∀ x, x ∈ (S : Set V) ↔ p x ∈ (S : Set V) := by
    intro p hp x
    obtain ⟨g, rfl⟩ := hp
    exact hinvariant g x
  have hmatch : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (OP1525Bridge.color A (g x)) (decide (g x = w)) =
        xor (xor (F x) (decide (x = π w))) d := by
    intro w
    obtain ⟨g, d, hg⟩ := hcolors w
    refine ⟨g.toEquiv, ⟨g, rfl⟩, d, ?_⟩
    intro x
    simpa [flipped] using hg x
  obtain ⟨p, ⟨g, rfl⟩, d, hd⟩ :=
    OP1525MonoPoly.reconstruct_of_invariant_monochrome (OP1525Bridge.color A) F P (S : Set V)
      a b c ha hb hc hab hac hbc u v huS hvS huv hA hpres π hmatch
  exact hlift g d hd
