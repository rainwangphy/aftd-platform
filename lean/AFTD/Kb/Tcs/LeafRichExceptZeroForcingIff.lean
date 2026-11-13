import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLeafRichExcept
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# leaf_rich_except_zero_forcing_iff

Topic: graphs   Node: 87e6d3858b14

Provenance: helper lemma. Structural helper for a leaf-rich graph case of OP-1399; experiment 24666 checks the resulting count against direct forcing on small graphs.

In a graph leaf-rich away from r, a set is zero forcing exactly when it contains all but at most one leaf at each support, and either contains r or has a neighbor of r all of whose leaves other than r are initially colored.
-/

open SimpleGraph

section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem unique_leaf_neighbor (x v y : V) (hx : G.degree x = 1)
    (hxv : G.Adj x v) (hxy : G.Adj x y) : y = v := by
  obtain ⟨z, hz, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hx
  exact (huniq y hxy).trans (huniq v hxv).symm

private theorem leaf_initial_forces (S : Set V) (x v : V)
    (hx : G.degree x = 1) (hxv : G.Adj x v) (hxS : x ∈ S) :
    ZeroForced G S v := by
  apply ZeroForced.step x v (ZeroForced.init x hxS) hxv
  intro y hxy hyv
  exact False.elim (hyv (unique_leaf_neighbor G x v y hx hxv hxy))

private theorem two_neighbors_degree (v x y : V) (hxy : x ≠ y)
    (hvx : G.Adj v x) (hvy : G.Adj v y) : 2 ≤ G.degree v := by
  have hpos : 0 < G.degree v := hvx.degree_pos_left
  have hne : G.degree v ≠ 1 := by
    intro hdeg
    exact hxy (unique_leaf_neighbor G v x y hdeg hvx hvy).symm
  omega

private theorem leaf_rich_conditions_suffice (r : V)
    (hG : graph_leaf_rich_except G r) (S : Set V)
    (hpair : ∀ v x y : V, x ≠ y → x ≠ r → y ≠ r → G.Adj v x →
      G.Adj v y → G.degree x = 1 → G.degree y = 1 → x ∈ S ∨ y ∈ S)
    (hroot : r ∈ S ∨ ∃ v : V, G.Adj v r ∧ 2 ≤ G.degree v ∧
      ∀ x : V, x ≠ r → G.Adj v x → G.degree x = 1 → x ∈ S) :
    is_zero_forcing_set G S := by
  classical
  have support_forced : ∀ v : V, v ≠ r → 2 ≤ G.degree v → ZeroForced G S v := by
    intro v hvr hvdeg
    rcases hG v hvr with ⟨hvone, _⟩ | ⟨x, y, hxy, hxr, hyr, hvx, hvy, hxd, hyd⟩
    · omega
    · rcases hpair v x y hxy hxr hyr hvx hvy hxd hyd with hxS | hyS
      · exact leaf_initial_forces G S x v hxd hvx.symm hxS
      · exact leaf_initial_forces G S y v hyd hvy.symm hyS
  have root_forced : ZeroForced G S r := by
    rcases hroot with hrS | ⟨v, hvr, hvdeg, hall⟩
    · exact ZeroForced.init r hrS
    · have hvne : v ≠ r := G.ne_of_adj hvr
      apply ZeroForced.step v r (support_forced v hvne hvdeg) hvr
      intro x hvx hxr
      rcases hG x hxr with ⟨hxd, _⟩ | ⟨a, b, hab, har, hbr, hxa, hxb, had, hbd⟩
      · exact ZeroForced.init x (hall x hxr hvx hxd)
      · exact support_forced x hxr (two_neighbors_degree G x a b hab hxa hxb)
  intro v
  by_cases hvr : v = r
  · subst v
    exact root_forced
  · rcases hG v hvr with ⟨hvd, u, hur, hvu, hud⟩ |
      ⟨x, y, hxy, hxr, hyr, hvx, hvy, hxd, hyd⟩
    · by_cases hvS : v ∈ S
      · exact ZeroForced.init v hvS
      · have hu_forced : ZeroForced G S u := support_forced u hur hud
        apply ZeroForced.step u v hu_forced hvu.symm
        intro x hux hxv
        by_cases hxr : x = r
        · subst x
          exact root_forced
        · rcases hG x hxr with ⟨hxd, _⟩ | ⟨a, b, hab, har, hbr, hxa, hxb, had, hbd⟩
          · rcases hpair u x v hxv hxr hvr hux hvu.symm hxd hvd with hxS | hvS'
            · exact ZeroForced.init x hxS
            · exact False.elim (hvS hvS')
          · exact support_forced x hxr (two_neighbors_degree G x a b hab hxa hxb)
    · exact support_forced v hvr (two_neighbors_degree G v x y hxy hvx hvy)
end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem fort_obstructs (S F : Set V)
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

private theorem rich_root_no_leaf_neighbor (r x : V)
    (hG : graph_leaf_rich_except G r) (hrx : G.Adj r x) :
    G.degree x ≠ 1 := by
  intro hxd
  have hxr : x ≠ r := (G.ne_of_adj hrx).symm
  rcases hG x hxr with ⟨_, u, hur, hxu, _⟩ |
    ⟨a, b, hab, har, hbr, hxa, hxb, had, hbd⟩
  · have hur' : u = r := unique_leaf_neighbor G x r u hxd hrx.symm hxu
    exact hur hur'
  · have htwo := two_neighbors_degree G x a b hab hxa hxb
    omega

private theorem rich_root_neighbor_degree (r v : V)
    (hG : graph_leaf_rich_except G r) (hvr : G.Adj v r) :
    2 ≤ G.degree v := by
  have hpos : 0 < G.degree v := hvr.degree_pos_left
  have hne : G.degree v ≠ 1 := rich_root_no_leaf_neighbor G r v hG hvr.symm
  omega

private theorem leaf_rich_conditions_necessary (r : V)
    (hG : graph_leaf_rich_except G r) (S : Set V)
    (hS : is_zero_forcing_set G S) :
    (∀ v x y : V, x ≠ y → x ≠ r → y ≠ r → G.Adj v x →
      G.Adj v y → G.degree x = 1 → G.degree y = 1 → x ∈ S ∨ y ∈ S) ∧
    (r ∈ S ∨ ∃ v : V, G.Adj v r ∧ 2 ≤ G.degree v ∧
      ∀ x : V, x ≠ r → G.Adj v x → G.degree x = 1 → x ∈ S) := by
  classical
  constructor
  · intro v x y hxy hxr hyr hvx hvy hxd hyd
    by_contra hnot
    push_neg at hnot
    let F : Set V := {w | w = x ∨ w = y}
    have hdisj : ∀ w, w ∈ F → w ∉ S := by
      intro w hw
      rcases hw with rfl | rfl
      · exact hnot.1
      · exact hnot.2
    have hfort : ∀ u, u ∉ F → ∀ w, w ∈ F → G.Adj u w →
        ∃ z, z ∈ F ∧ G.Adj u z ∧ z ≠ w := by
      intro u hu w hw huw
      rcases hw with hwx | hwy
      · subst w
        have huv : u = v := unique_leaf_neighbor G x v u hxd hvx.symm huw.symm
        subst u
        exact ⟨y, Or.inr rfl, hvy, hxy.symm⟩
      · subst w
        have huv : u = v := unique_leaf_neighbor G y v u hyd hvy.symm huw.symm
        subst u
        exact ⟨x, Or.inl rfl, hvx, hxy⟩
    exact (fort_obstructs G S F hdisj hfort x (hS x)) (Or.inl rfl)
  · by_contra hnot
    push_neg at hnot
    let F : Set V := {x | x = r ∨ (x ≠ r ∧ G.degree x = 1 ∧ x ∉ S ∧
      ∃ v, G.Adj v r ∧ G.Adj v x)}
    have hdisj : ∀ x, x ∈ F → x ∉ S := by
      intro x hx
      rcases hx with rfl | ⟨_, _, hxS, _⟩
      · exact hnot.1
      · exact hxS
    have hfort : ∀ u, u ∉ F → ∀ w, w ∈ F → G.Adj u w →
        ∃ x, x ∈ F ∧ G.Adj u x ∧ x ≠ w := by
      intro u hu w hw huw
      rcases hw with hwr' | ⟨hwr, hwd, hwS, v, hvr, hvw⟩
      · subst w
        obtain ⟨x, hxr, hux, hxd, hxS⟩ :=
          hnot.2 u huw (rich_root_neighbor_degree G r u hG huw)
        exact ⟨x, Or.inr ⟨hxr, hxd, hxS, u, huw, hux⟩, hux, hxr⟩
      · have huv : u = v := unique_leaf_neighbor G w v u hwd hvw.symm huw.symm
        subst u
        exact ⟨r, Or.inl rfl, hvr, hwr.symm⟩
    exact (fort_obstructs G S F hdisj hfort r (hS r)) (Or.inl rfl)
end

theorem leaf_rich_except_zero_forcing_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (hG : graph_leaf_rich_except G r) (S : Set V) : is_zero_forcing_set G S ↔ (∀ v x y : V, x ≠ y → x ≠ r → y ≠ r → G.Adj v x → G.Adj v y → G.degree x = 1 → G.degree y = 1 → x ∈ S ∨ y ∈ S) ∧ (r ∈ S ∨ ∃ v : V, G.Adj v r ∧ 2 ≤ G.degree v ∧ ∀ x : V, x ≠ r → G.Adj v x → G.degree x = 1 → x ∈ S) := by
  constructor
  · exact leaf_rich_conditions_necessary G r hG S
  · rintro ⟨hpair, hroot⟩
    exact leaf_rich_conditions_suffice G r hG S hpair hroot
