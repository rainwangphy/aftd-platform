import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsBalancedPartition
import AFTD.Kb.Tcs.SignedGraphIsReconstructible
import AFTD.Kb.Tcs.SignedGraphReconstructibleBalancedMonoInvariant
import AFTD.Kb.Tcs.SignedGraphSwitch
import AFTD.Kb.Tcs.SignedGraphSameDeck
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.G

/-!
# signed_graph_reconstructible_balanced_mono_pair_fixed

Topic: combinatorics   Node: 19d46960a33a

Provenance: original. Related work: A structural case of OP-1525, comparing arXiv:2611.13901, Section 4.1.

Let G be a connected balanced signed graph on at least seven vertices, with a specified balance partition. Suppose distinct vertices a and b lie in the same part and every automorphism of the underlying graph preserves the unordered pair {a, b}, and suppose a third vertex t, distinct from both a and b, is fixed by every automorphism of the underlying graph. Then G is determined up to signed-graph isomorphism among all finite signed graphs by the multiset obtained by switching the sign of every incident edge at each vertex.
-/

open OP1525MonoPoly

namespace OP1525PairFixed
variable {V : Type*} [DecidableEq V]

theorem reconstruct (A B : V → Bool) (P : Equiv.Perm V → Prop)
    (a b t : V) (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    (hA : A a = A b)
    (hinv : ∀ g, P g → ∀ x, (x = a ∨ x = b) ↔ (g x = a ∨ g x = b))
    (hfixed : ∀ g, P g → g t = t)
    (π : Equiv.Perm V) (w : V)
    (hw : w ≠ a ∧ w ≠ b ∧ w ≠ t)
    (hπw : π w ≠ a ∧ π w ≠ b ∧ π w ≠ t)
    (hdeck : ∀ z, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (A (g x)) (decide (g x = z)) =
        xor (xor (B x) (decide (x = π z))) d) :
    ∃ g, P g ∧ ∃ d : Bool, ∀ x, A (g x) = xor (B x) d := by
  classical
  have hA' (x : V) (hx : x = a ∨ x = b) : A x = A a := by
    rcases hx with rfl | rfl <;> simp [hA]
  obtain ⟨g₀, hg₀, d₀, h₀⟩ := hdeck w
  have hg₀a : g₀ a = a ∨ g₀ a = b := (hinv g₀ hg₀ a).mp (Or.inl rfl)
  have hg₀b : g₀ b = a ∨ g₀ b = b := (hinv g₀ hg₀ b).mp (Or.inr rfl)
  have h₀a : A a = xor (B a) d₀ := by
    have he := h₀ a
    have hne : g₀ a ≠ w := by rcases hg₀a with h | h <;> rw [h] <;> first | exact Ne.symm hw.1 | exact Ne.symm hw.2.1
    simpa [hA' (g₀ a) hg₀a, hne, Ne.symm hπw.1] using he
  have h₀b : A a = xor (B b) d₀ := by
    have he := h₀ b
    have hne : g₀ b ≠ w := by rcases hg₀b with h | h <;> rw [h] <;> first | exact Ne.symm hw.1 | exact Ne.symm hw.2.1
    simpa [hA' (g₀ b) hg₀b, hne, Ne.symm hπw.2.1] using he
  have h₀t : A t = xor (B t) d₀ := by
    have he := h₀ t
    simpa [hfixed g₀ hg₀, Ne.symm hw.2.2, Ne.symm hπw.2.2] using he
  have hB : B a = B b := xor_cancel_common _ _ d₀ (h₀a.symm.trans h₀b)
  have hrel : xor (A a) (A t) = xor (B a) (B t) := by
    rw [h₀a, h₀t]
    cases B a <;> cases B t <;> cases d₀ <;> decide
  obtain ⟨g, hg, d, heq⟩ := hdeck a
  have hga : g a = a ∨ g a = b := (hinv g hg a).mp (Or.inl rfl)
  have hgb : g b = a ∨ g b = b := (hinv g hg b).mp (Or.inr rfl)
  have hgdistinct : g a ≠ g b := fun he => hab (g.injective he)
  have hπa : π a = a ∨ π a = b := by
    by_contra hn
    push_neg at hn
    have ha' : xor (A a) (decide (g a = a)) = xor (B a) d := by
      simpa [hA' (g a) hga, Ne.symm hn.1] using heq a
    have hb' : xor (A a) (decide (g b = a)) = xor (B a) d := by
      simpa [hA' (g b) hgb, Ne.symm hn.2, hB] using heq b
    have hd' : decide (g a = a) = decide (g b = a) := by
      apply xor_cancel_common _ _ (A a)
      simpa [Bool.xor_comm] using ha'.trans hb'.symm
    have hor : g a = a ∨ g b = a := by
      rcases hga with ha | ha
      · exact Or.inl ha
      · rcases hgb with hb | hb
        · exact Or.inr hb
        · exact False.elim (hgdistinct (ha.trans hb.symm))
    rcases hor with ha | hb
    · have hb : g b ≠ a := fun h => hgdistinct (ha.trans h.symm)
      simp [ha, hb] at hd'
    · have ha : g a ≠ a := fun h => hgdistinct (h.trans hb.symm)
      simp [ha, hb] at hd'
  have hπat : π a ≠ t := by
    intro h
    rcases hπa with ha | hb
    · exact hta (h.symm.trans ha)
    · exact htb (h.symm.trans hb)
  have ht : A t = xor (B t) d := by
    have he := heq t
    simpa [hfixed g hg, hta, Ne.symm hπat] using he
  have hAa : A a = xor (B a) d := by
    cases hA0 : A a <;> cases hAt : A t <;> cases hB0 : B a <;>
      cases hBt : B t <;> cases hd : d <;> simp_all
  let q := g.symm a
  have hgq : g q = a := by simp [q]
  have hq : q = a ∨ q = b := (hinv g hg q).mpr (Or.inl hgq)
  have hBq : B q = B a := by
    rcases hq with h | h
    · rw [h]
    · rw [h, ← hB]
  have hmatch : q = π a := by
    by_contra hn
    have he := heq q
    rw [hgq, hBq, hAa] at he
    cases hBa : B a <;> cases hd : d <;> simp [hn, hBa, hd] at he
  refine ⟨g, hg, d, ?_⟩
  intro x
  have he : (g x = a) ↔ x = π a := by
    constructor
    · intro hh
      have : g x = g q := hh.trans hgq.symm
      exact (g.injective this).trans hmatch
    · intro hh
      rw [← hmatch] at hh
      simpa [hh] using hgq
  have hx := heq x
  rw [show decide (g x = a) = decide (x = π a) by simp only [he]] at hx
  exact xor_cancel_flip _ _ _ _ hx

end OP1525PairFixed

open OP1525Bridge

theorem signed_graph_reconstructible_balanced_mono_pair_fixed {V : Type*} [DecidableEq V] [Fintype V]
    (G : SignedGraph V) (hconn : G.graph.Connected)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B)
    (a b t : V) (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    (hsize : Fintype.card V ≥ 7) (hmono : a ∈ A ↔ b ∈ A)
    (hinv : ∀ g : G.graph ≃g G.graph, ∀ x, (x = a ∨ x = b) ↔ (g x = a ∨ g x = b))
    (hfixed : ∀ g : G.graph ≃g G.graph, g t = t) : G.IsReconstructible := by
  classical
  unfold SignedGraph.IsReconstructible
  intro W _ _ H hdeck
  obtain ⟨π₀, hcards⟩ := hdeck
  obtain ⟨F, π, hcolors, hlift⟩ := deck_color_model G H hconn A B hbal π₀ hcards a
  let P : Equiv.Perm V → Prop := fun p => ∃ g : G.graph ≃g G.graph, g.toEquiv = p
  have hp : ∀ p, P p → ∀ x, (x = a ∨ x = b) ↔ (p x = a ∨ p x = b) := by
    intro p hp x
    obtain ⟨g, rfl⟩ := hp
    exact hinv g x
  have hfix : ∀ p, P p → p t = t := by
    intro p hp
    obtain ⟨g, rfl⟩ := hp
    exact hfixed g
  have hmatch : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (OP1525Bridge.color A (g x)) (decide (g x = w)) =
        xor (xor (F x) (decide (x = π w))) d := by
    intro w
    obtain ⟨g, d, hg⟩ := hcolors w
    refine ⟨g.toEquiv, ⟨g, rfl⟩, d, ?_⟩
    intro x
    simpa [flipped] using hg x
  let anchors : Finset V := {a, b, t}
  let bad : Finset V := anchors ∪ anchors.image π.symm
  have ha : anchors.card ≤ 3 := Finset.card_le_three
  have hb : bad.card ≤ 6 := by
    have hu := Finset.card_union_le anchors (anchors.image π.symm)
    have hi := Finset.card_image_le (s := anchors) (f := π.symm)
    dsimp [bad]
    omega
  have hv : ∃ v, v ∉ bad := by
    by_contra h
    push_neg at h
    have he : bad = Finset.univ := by
      ext x
      simp [h x]
    have hc := congrArg Finset.card he
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨v, hv⟩ := hv
  have hvn : v ≠ a ∧ v ≠ b ∧ v ≠ t := by
    have h : v ∉ anchors := fun h => hv (Finset.mem_union_left _ h)
    simpa [anchors] using h
  have hvp : π v ≠ a ∧ π v ≠ b ∧ π v ≠ t := by
    have hnot : v ∉ anchors.image π.symm := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hh : π v ∉ anchors := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨π v, h, by simp⟩
    simpa [anchors] using hh
  have hA : OP1525Bridge.color A a = OP1525Bridge.color A b := by
    simp [OP1525Bridge.color, hmono]
  obtain ⟨p, ⟨g, rfl⟩, d, hd⟩ := OP1525PairFixed.reconstruct
    (OP1525Bridge.color A) F P a b t hab hta htb hA hp hfix π v hvn hvp hmatch
  exact hlift g d hd
