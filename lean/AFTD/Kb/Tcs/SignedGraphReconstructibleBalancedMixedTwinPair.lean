import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsBalancedPartition
import AFTD.Kb.Tcs.SignedGraphIsReconstructible
import AFTD.Kb.Tcs.SignedGraphReconstructibleBalancedMonoInvariant
import AFTD.Kb.Tcs.SignedGraphSwitch
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraphSameDeck
import AFTD.Kb.Tcs.G

/-!
# signed_graph_reconstructible_balanced_mixed_twin_pair

Topic: combinatorics   Node: f880699e5d7b

Provenance: original. Related work: A mixed twin-pair structural subcase of OP-1525, compared with arXiv:2611.13901 Section 4.1.

Let G be a connected balanced signed graph on at least five vertices, with a specified balance partition. Suppose distinct vertices a and b lie in different parts, every automorphism of the underlying graph preserves the unordered pair {a, b}, and the permutation that swaps exactly a and b is itself an automorphism of the underlying graph. Then G is determined up to signed-graph isomorphism among all finite signed graphs by its vertex-switching deck: a bijection that matches every one-vertex-switched card of G to an isomorphic switched card of another signed graph H implies that G and H are isomorphic.
-/

open OP1525MonoPoly

namespace OP1525MixedTwinPair
variable {V : Type*} [DecidableEq V]

theorem reconstruct (A B : V → Bool) (P : Equiv.Perm V → Prop)
    (a b : V) (hab : a ≠ b) (hA : A a ≠ A b)
    (hinv : ∀ g, P g → ∀ x, (x = a ∨ x = b) ↔ (g x = a ∨ g x = b))
    (hswap : ∀ g, P g → P (g.trans (Equiv.swap a b)))
    (π : Equiv.Perm V) (w : V)
    (hw : w ≠ a ∧ w ≠ b) (hπw : π w ≠ a ∧ π w ≠ b)
    (hdeck : ∀ z, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (A (g x)) (decide (g x = z)) =
        xor (xor (B x) (decide (x = π z))) d) :
    ∃ g, P g ∧ ∃ d : Bool, ∀ x, A (g x) = xor (B x) d := by
  classical
  have hneg (x : V) (hx : x = a ∨ x = b) : A (Equiv.swap a b x) = !(A x) := by
    rcases hx with hx | hx <;> rw [hx]
    · cases ha : A a <;> cases hb : A b <;> simp [ha, hb] at hA ⊢
    · cases ha : A a <;> cases hb : A b <;> simp [ha, hb] at hA ⊢
  obtain ⟨g₀, hg₀, d₀, h₀⟩ := hdeck w
  have hg₀a : g₀ a = a ∨ g₀ a = b := (hinv g₀ hg₀ a).mp (Or.inl rfl)
  have hg₀b : g₀ b = a ∨ g₀ b = b := (hinv g₀ hg₀ b).mp (Or.inr rfl)
  have hdistinct : g₀ a ≠ g₀ b := fun hh => hab (g₀.injective hh)
  have hdiff : A (g₀ a) ≠ A (g₀ b) := by
    rcases hg₀a with ha | ha <;> rcases hg₀b with hb | hb
    · exact False.elim (hdistinct (ha.trans hb.symm))
    · simpa [ha, hb] using hA
    · simpa [ha, hb] using Ne.symm hA
    · exact False.elim (hdistinct (ha.trans hb.symm))
  have ha₀ : A (g₀ a) = xor (B a) d₀ := by
    have hne : g₀ a ≠ w := by rcases hg₀a with h | h <;> rw [h] <;> first | exact Ne.symm hw.1 | exact Ne.symm hw.2
    simpa [hne, Ne.symm hπw.1] using h₀ a
  have hb₀ : A (g₀ b) = xor (B b) d₀ := by
    have hne : g₀ b ≠ w := by rcases hg₀b with h | h <;> rw [h] <;> first | exact Ne.symm hw.1 | exact Ne.symm hw.2
    simpa [hne, Ne.symm hπw.2] using h₀ b
  have hB : B a ≠ B b := by
    intro he
    apply hdiff
    rw [ha₀, hb₀, he]
  obtain ⟨g, hg, d, heq⟩ := hdeck a
  have hga : g a = a ∨ g a = b := (hinv g hg a).mp (Or.inl rfl)
  have hgb : g b = a ∨ g b = b := (hinv g hg b).mp (Or.inr rfl)
  have hga_ne : g a ≠ g b := fun hh => hab (g.injective hh)
  have hπa : π a = a ∨ π a = b := by
    by_contra hn
    push_neg at hn
    have ea := heq a
    have eb := heq b
    rcases hga with ha | ha <;> rcases hgb with hb | hb
    · exact hga_ne (ha.trans hb.symm)
    · simp only [ha, hb, hab, Ne.symm hab, decide_true, decide_false,
        Ne.symm hn.1, Ne.symm hn.2, Bool.xor_false] at ea eb
      cases hAa : A a <;> cases hAb : A b <;> cases hBa : B a <;>
        cases hBb : B b <;> cases hd : d <;>
          simp [hAa, hAb, hBa, hBb, hd] at hA hB ea eb
    · simp only [ha, hb, hab, Ne.symm hab, decide_true, decide_false,
        Ne.symm hn.1, Ne.symm hn.2, Bool.xor_false] at ea eb
      cases hAa : A a <;> cases hAb : A b <;> cases hBa : B a <;>
        cases hBb : B b <;> cases hd : d <;>
          simp [hAa, hAb, hBa, hBb, hd] at hA hB ea eb
    · exact hga_ne (ha.trans hb.symm)
  let q := g.symm a
  have hgq : g q = a := by simp [q]
  have hq : q = a ∨ q = b := (hinv g hg q).mpr (Or.inl hgq)
  have hequiv (x : V) : (g x = a) ↔ x = q := by
    constructor
    · intro h
      exact g.injective (h.trans hgq.symm)
    · intro h
      rw [h, hgq]
  by_cases hmatch : q = π a
  · refine ⟨g, hg, d, ?_⟩
    intro x
    have hx := heq x
    rw [show decide (g x = a) = decide (x = π a) by simp only [hequiv, hmatch]] at hx
    exact xor_cancel_flip _ _ _ _ hx
  · let g' : Equiv.Perm V := g.trans (Equiv.swap a b)
    have hg' : P g' := hswap g hg
    refine ⟨g', hg', d, ?_⟩
    intro x
    by_cases hx : x = a ∨ x = b
    · have hgx : g x = a ∨ g x = b := (hinv g hg x).mp hx
      have hcomp : (x = q) ↔ x ≠ π a := by
        rcases hq with hq | hq <;> rcases hπa with hp | hp <;>
          rcases hx with hx | hx <;>
          simp [hq, hp, hx, hab, Ne.symm hab] at hmatch ⊢
      have hdec : decide (g x = a) = !(decide (x = π a)) := by
        by_cases he : x = π a
        · have hnot : x ≠ q := by
            intro h
            exact (hcomp.mp h) he
          have hga : g x ≠ a := fun h => hnot ((hequiv x).mp h)
          subst x
          simp [hga]
        · have hxq : x = q := hcomp.mpr he
          have hga : g x = a := (hequiv x).mpr hxq
          simp [hga, he]
      have he := heq x
      rw [hdec] at he
      change A (Equiv.swap a b (g x)) = xor (B x) d
      rw [hneg (g x) hgx]
      cases ha : A (g x) <;> cases hb : B x <;> cases hc : d <;>
        cases hd : decide (x = π a) <;> simp [ha, hb, hc, hd] at he ⊢
    · have hgx : ¬(g x = a ∨ g x = b) := fun h => hx ((hinv g hg x).mpr h)
      have hxa : g x ≠ a := fun h => hgx (Or.inl h)
      have hxb : g x ≠ b := fun h => hgx (Or.inr h)
      have hxp : x ≠ π a := by intro h; apply hx; rw [h]; exact hπa
      change A (Equiv.swap a b (g x)) = xor (B x) d
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      simpa [hxa, hxp] using heq x

end OP1525MixedTwinPair

#print axioms OP1525MixedTwinPair.reconstruct

open OP1525Bridge

theorem signed_graph_reconstructible_balanced_mixed_twin_pair {V : Type*} [DecidableEq V] [Fintype V]
    (G : SignedGraph V) (hconn : G.graph.Connected)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B)
    (a b : V) (hab : a ≠ b) (hsize : Fintype.card V ≥ 5)
    (hmixed : (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A))
    (hinv : ∀ g : G.graph ≃g G.graph, ∀ x, (x = a ∨ x = b) ↔ (g x = a ∨ g x = b))
    (τ : G.graph ≃g G.graph) (hτ : τ.toEquiv = Equiv.swap a b) : G.IsReconstructible := by
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
  have hswap : ∀ p, P p → P (p.trans (Equiv.swap a b)) := by
    intro p hp
    obtain ⟨g, rfl⟩ := hp
    refine ⟨g.trans τ, ?_⟩
    change g.toEquiv.trans τ.toEquiv = _
    rw [hτ]
  have hmatch : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (OP1525Bridge.color A (g x)) (decide (g x = w)) =
        xor (xor (F x) (decide (x = π w))) d := by
    intro w
    obtain ⟨g, d, hg⟩ := hcolors w
    refine ⟨g.toEquiv, ⟨g, rfl⟩, d, ?_⟩
    intro x
    simpa [flipped] using hg x
  let anchors : Finset V := {a, b}
  let bad : Finset V := anchors ∪ anchors.image π.symm
  have ha : anchors.card ≤ 2 := Finset.card_le_two
  have hb : bad.card ≤ 4 := by
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
  have hvn : v ≠ a ∧ v ≠ b := by
    have h : v ∉ anchors := fun h => hv (Finset.mem_union_left _ h)
    simpa [anchors] using h
  have hvp : π v ≠ a ∧ π v ≠ b := by
    have hnot : v ∉ anchors.image π.symm := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hh : π v ∉ anchors := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨π v, h, by simp⟩
    simpa [anchors] using hh
  have hA : OP1525Bridge.color A a ≠ OP1525Bridge.color A b := by
    rcases hmixed with h | h <;> simp [OP1525Bridge.color, h.1, h.2]
  obtain ⟨p, ⟨g, rfl⟩, d, hd⟩ := OP1525MixedTwinPair.reconstruct
    (OP1525Bridge.color A) F P a b hab hA hp hswap π v hvn hvp hmatch
  exact hlift g d hd
