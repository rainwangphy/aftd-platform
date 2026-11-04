import AFTD.Prelude

/-!
# digraph_four_vertices_kernel_perfect_triple

Topic: graphs   Node: e2d27f8f5071

Provenance: helper lemma. Finite local consequence of kernel-perfect set theory, motivated by Lemma 14 in https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p53/pdf/ and checked by exhaustive computation 14074.

Every four-vertex induced subdigraph of a loopless digraph contains a kernel-perfect three-vertex set through any prescribed vertex.
-/

lemma digraph_four_vertices_kernel_perfect_triple_finish
    {α : Type} [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (S : Finset α) (x u v : α) (hx : x ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (hker : ∃ K : Finset α, K ⊆ ({x, u, v} : Finset α) ∧
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b → ¬ D.Adj a b) ∧
      (∀ b ∈ ({x, u, v} : Finset α), ∃ a ∈ K, a = b ∨ D.Adj a b)) :
    ∃ T : Finset α, T ⊆ S ∧ x ∈ T ∧ T.card = 3 ∧
      (∀ U : Finset α, U ⊆ T → ∃ K : Finset α, K ⊆ U ∧
        (∀ a ∈ K, ∀ b ∈ K, a ≠ b → ¬ D.Adj a b) ∧
        (∀ b ∈ U, ∃ a ∈ K, a = b ∨ D.Adj a b)) := by
  refine ⟨{x, u, v}, ?_, by simp, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  · exact Finset.card_eq_three.mpr ⟨x, u, v, hxu, hxv, huv, rfl⟩
  · intro U hU
    by_cases hUc : U.card ≤ 2
    · interval_cases hc : U.card
      · have : U = ∅ := Finset.card_eq_zero.mp hc
        subst this
        refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
        · intro a ha; simp at ha
        · intro b hb; simp at hb
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        refine ⟨{a}, Finset.Subset.refl _, ?_, ?_⟩
        · intro a' ha' b' hb' hab'
          simp only [Finset.mem_singleton] at ha' hb'; subst ha' hb'; exact (hab' rfl).elim
        · intro b hb
          simp only [Finset.mem_singleton] at hb ⊢
          exact ⟨a, rfl, Or.inl hb.symm⟩
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
        by_cases hab_adj : D.Adj a b
        · refine ⟨{a}, by simp, ?_, ?_⟩
          · intro a' ha' b' hb' hab'
            simp only [Finset.mem_singleton] at ha' hb'; subst ha' hb'; exact (hab' rfl).elim
          · intro b' hb'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
            refine ⟨a, by simp, ?_⟩
            rcases hb' with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr hab_adj
        · by_cases hba_adj : D.Adj b a
          · refine ⟨{b}, by simp, ?_, ?_⟩
            · intro a' ha' b' hb' hab'
              simp only [Finset.mem_singleton] at ha' hb'; subst ha' hb'; exact (hab' rfl).elim
            · intro b' hb'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
              refine ⟨b, by simp, ?_⟩
              rcases hb' with rfl | rfl
              · exact Or.inr hba_adj
              · exact Or.inl rfl
          · refine ⟨{a, b}, Finset.Subset.refl _, ?_, ?_⟩
            · intro a' ha' b' hb' hab'
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
              rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
              · exact (hab' rfl).elim
              · exact hab_adj
              · exact hba_adj
              · exact (hab' rfl).elim
            · intro b' hb'
              exact ⟨b', hb', Or.inl rfl⟩
    · have : U = {x, u, v} := Finset.eq_of_subset_of_card_le hU (by
        rw [Finset.card_eq_three.mpr ⟨x, u, v, hxu, hxv, huv, rfl⟩]
        omega)
      subst this
      exact hker

lemma digraph_four_vertices_kernel_perfect_triple_out_two
    {α : Type} [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (x a b : α) (hxa : D.Adj x a) (hxb : D.Adj x b) :
    ∃ K : Finset α, K ⊆ ({x, a, b} : Finset α) ∧
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ ({x, a, b} : Finset α), ∃ u ∈ K, u = v ∨ D.Adj u v) := by
  refine ⟨{x}, by simp, ?_, ?_⟩
  · intro u hu v hv huv
    simp only [Finset.mem_singleton] at hu hv; subst hu hv; exact (huv rfl).elim
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with ha | hb | hc
    · exact ⟨x, by simp, Or.inl ha.symm⟩
    · exact ⟨x, by simp, Or.inr (hb ▸ hxa)⟩
    · exact ⟨x, by simp, Or.inr (hc ▸ hxb)⟩

lemma digraph_four_vertices_kernel_perfect_triple_in_two
    {α : Type} [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (x a b : α) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (hax_adj : D.Adj a x) (hbx_adj : D.Adj b x) :
    ∃ K : Finset α, K ⊆ ({x, a, b} : Finset α) ∧
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ ({x, a, b} : Finset α), ∃ u ∈ K, u = v ∨ D.Adj u v) := by
  by_cases hab_adj : D.Adj a b
  · refine ⟨{a}, by simp, ?_, ?_⟩
    · intro u hu v hv huv; simp at hu hv; subst hu hv; exact (huv rfl).elim
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hx_eq | ha_eq | hb_eq
      · exact ⟨a, by simp, Or.inr (hx_eq ▸ hax_adj)⟩
      · exact ⟨a, by simp, Or.inl ha_eq.symm⟩
      · exact ⟨a, by simp, Or.inr (hb_eq ▸ hab_adj)⟩
  · by_cases hba_adj : D.Adj b a
    · refine ⟨{b}, by simp, ?_, ?_⟩
      · intro u hu v hv huv; simp at hu hv; subst hu hv; exact (huv rfl).elim
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with hx_eq | ha_eq | hb_eq
        · exact ⟨b, by simp, Or.inr (hx_eq ▸ hbx_adj)⟩
        · exact ⟨b, by simp, Or.inr (ha_eq ▸ hba_adj)⟩
        · exact ⟨b, by simp, Or.inl hb_eq.symm⟩
    · refine ⟨{a, b}, by simp, ?_, ?_⟩
      · intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact (huv rfl).elim
        · exact hab_adj
        · exact hba_adj
        · exact (huv rfl).elim
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with hx_eq | ha_eq | hb_eq
        · exact ⟨a, by simp, Or.inr (hx_eq ▸ hax_adj)⟩
        · exact ⟨a, by simp, Or.inl ha_eq.symm⟩
        · exact ⟨b, by simp, Or.inl hb_eq.symm⟩

lemma digraph_four_vertices_kernel_perfect_triple_indep_pair
    {α : Type} [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (a b c : α) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h_ind : ¬ D.Adj a b ∧ ¬ D.Adj b a) :
    ∃ K : Finset α, K ⊆ ({a, b, c} : Finset α) ∧
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ ({a, b, c} : Finset α), ∃ u ∈ K, u = v ∨ D.Adj u v) := by
  by_cases h : D.Adj a c ∨ D.Adj b c
  · refine ⟨{a, b}, by simp, ?_, ?_⟩
    · intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (huv rfl).elim
      · exact h_ind.1
      · exact h_ind.2
      · exact (huv rfl).elim
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with ha | hb | hc
      · exact ⟨a, by simp, Or.inl ha.symm⟩
      · exact ⟨b, by simp, Or.inl hb.symm⟩
      · rcases h with hac | hbc_adj
        · exact ⟨a, by simp, Or.inr (hc ▸ hac)⟩
        · exact ⟨b, by simp, Or.inr (hc ▸ hbc_adj)⟩
  · have hnac : ¬ D.Adj a c := fun h1 => h (Or.inl h1)
    have hnbc : ¬ D.Adj b c := fun h2 => h (Or.inr h2)
    by_cases hca_adj : D.Adj c a
    · by_cases hcb_adj : D.Adj c b
      · refine ⟨{c}, by simp, ?_, ?_⟩
        · intro u hu v hv huv; simp at hu hv; subst hu hv; exact (huv rfl).elim
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with ha | hb | hc
          · exact ⟨c, by simp, Or.inr (ha ▸ hca_adj)⟩
          · exact ⟨c, by simp, Or.inr (hb ▸ hcb_adj)⟩
          · exact ⟨c, by simp, Or.inl hc.symm⟩
      · refine ⟨{b, c}, by simp, ?_, ?_⟩
        · intro u hu v hv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact (huv rfl).elim
          · exact hnbc
          · exact hcb_adj
          · exact (huv rfl).elim
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with ha | hb | hc
          · exact ⟨c, by simp, Or.inr (ha ▸ hca_adj)⟩
          · exact ⟨b, by simp, Or.inl hb.symm⟩
          · exact ⟨c, by simp, Or.inl hc.symm⟩
    · by_cases hcb_adj : D.Adj c b
      · refine ⟨{a, c}, by simp, ?_, ?_⟩
        · intro u hu v hv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact (huv rfl).elim
          · exact hnac
          · exact hca_adj
          · exact (huv rfl).elim
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with ha | hb | hc
          · exact ⟨a, by simp, Or.inl ha.symm⟩
          · exact ⟨c, by simp, Or.inr (hb ▸ hcb_adj)⟩
          · exact ⟨c, by simp, Or.inl hc.symm⟩
      · refine ⟨{a, b, c}, by simp, ?_, ?_⟩
        · intro u hu v hv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
          · exact (huv rfl).elim
          · exact h_ind.1
          · exact hnac
          · exact h_ind.2
          · exact (huv rfl).elim
          · exact hnbc
          · exact hca_adj
          · exact hcb_adj
          · exact (huv rfl).elim
        · intro v hv
          exact ⟨v, hv, Or.inl rfl⟩

theorem digraph_four_vertices_kernel_perfect_triple
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (S : Finset α) (hS : S.card = 4)
    (x : α) (hx : x ∈ S) :
    ∃ T : Finset α, T ⊆ S ∧ x ∈ T ∧ T.card = 3 ∧
      (∀ U : Finset α, U ⊆ T → ∃ K : Finset α, K ⊆ U ∧
        (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
        (∀ v ∈ U, ∃ u ∈ K, u = v ∨ D.Adj u v)) := by
  have hc : (S.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx, hS]
  obtain ⟨y, z, w, hyz, hyw, hzw, he⟩ := Finset.card_eq_three.mp hc
  have hx_not : x ∉ S.erase x := Finset.notMem_erase x S
  rw [he] at hx_not
  have hxy : x ≠ y := by intro h; subst h; exact hx_not (by simp)
  have hxz : x ≠ z := by intro h; subst h; exact hx_not (by simp)
  have hxw : x ≠ w := by intro h; subst h; exact hx_not (by simp)
  have hyS : y ∈ S := Finset.mem_of_mem_erase (by rw [he]; simp)
  have hzS : z ∈ S := Finset.mem_of_mem_erase (by rw [he]; simp)
  have hwS : w ∈ S := Finset.mem_of_mem_erase (by rw [he]; simp)
  by_cases hind_y : ¬ D.Adj x y ∧ ¬ D.Adj y x
  · have hker := digraph_four_vertices_kernel_perfect_triple_indep_pair D x y z hxy hyz hxz.symm hind_y
    exact digraph_four_vertices_kernel_perfect_triple_finish D S x y z hx hyS hzS hxy hxz hyz hker
  · by_cases hind_z : ¬ D.Adj x z ∧ ¬ D.Adj z x
    · have hker := digraph_four_vertices_kernel_perfect_triple_indep_pair D x z y hxz hyz.symm hxy.symm hind_z
      exact digraph_four_vertices_kernel_perfect_triple_finish D S x z y hx hzS hyS hxz hxy hyz.symm hker
    · by_cases hind_w : ¬ D.Adj x w ∧ ¬ D.Adj w x
      · have hker := digraph_four_vertices_kernel_perfect_triple_indep_pair D x w y hxw hyw.symm hxy.symm hind_w
        exact digraph_four_vertices_kernel_perfect_triple_finish D S x w y hx hwS hyS hxw hxy hyw.symm hker
      · by_cases hxy_out : D.Adj x y
        · by_cases hxz_out : D.Adj x z
          · have hker := digraph_four_vertices_kernel_perfect_triple_out_two D x y z hxy_out hxz_out
            exact digraph_four_vertices_kernel_perfect_triple_finish D S x y z hx hyS hzS hxy hxz hyz hker
          · by_cases hxw_out : D.Adj x w
            · have hker := digraph_four_vertices_kernel_perfect_triple_out_two D x y w hxy_out hxw_out
              exact digraph_four_vertices_kernel_perfect_triple_finish D S x y w hx hyS hwS hxy hxw hyw hker
            · have hzx_adj : D.Adj z x := by by_contra h; exact hind_z ⟨hxz_out, h⟩
              have hwx_adj : D.Adj w x := by by_contra h; exact hind_w ⟨hxw_out, h⟩
              have hker := digraph_four_vertices_kernel_perfect_triple_in_two D x z w hzw hxz.symm hxw.symm hzx_adj hwx_adj
              exact digraph_four_vertices_kernel_perfect_triple_finish D S x z w hx hzS hwS hxz hxw hzw hker
        · have hyx_adj : D.Adj y x := by by_contra h; exact hind_y ⟨hxy_out, h⟩
          by_cases hxz_out : D.Adj x z
          · by_cases hxw_out : D.Adj x w
            · have hker := digraph_four_vertices_kernel_perfect_triple_out_two D x z w hxz_out hxw_out
              exact digraph_four_vertices_kernel_perfect_triple_finish D S x z w hx hzS hwS hxz hxw hzw hker
            · have hwx_adj : D.Adj w x := by by_contra h; exact hind_w ⟨hxw_out, h⟩
              have hker := digraph_four_vertices_kernel_perfect_triple_in_two D x y w hyw hxy.symm hxw.symm hyx_adj hwx_adj
              exact digraph_four_vertices_kernel_perfect_triple_finish D S x y w hx hyS hwS hxy hxw hyw hker
          · have hzx_adj : D.Adj z x := by by_contra h; exact hind_z ⟨hxz_out, h⟩
            have hker := digraph_four_vertices_kernel_perfect_triple_in_two D x y z hyz hxy.symm hxz.symm hyx_adj hzx_adj
            exact digraph_four_vertices_kernel_perfect_triple_finish D S x y z hx hyS hzS hxy hxz hyz hker
