import AFTD.Prelude

/-!
# matching_blocked_short_switches_two_missing_saturation

Topic: graphs   Node: 928c5257128f

Provenance: helper lemma. OP-1957: local complement-neighborhood saturation forced by the failure of short alternating switches.

Let a perfect matching contain uv, where u has exactly the two nonneighbors a,b and v is adjacent to both. If no alternating four- or six-cycle through uv exists, the matching pairs a with b, and every vertex other than u,v,a,b is nonadjacent to v,a,b.
-/

theorem matching_blocked_short_switches_two_missing_saturation
    {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v a b : V) (huv : P.Adj u v) (hab : a ≠ b)
    (hau : a ≠ u) (hbu : b ≠ u) (hua : ¬ G.Adj u a) (hub : ¬ G.Adj u b)
    (honly : ∀ x : V, x ≠ u → ¬ G.Adj u x → x = a ∨ x = b)
    (hsep : ∀ x : V, x ≠ u → ¬ G.Adj u x → G.Adj v x)
    (h4 : ∀ x y : V, Function.Injective (![u,v,x,y] : Fin 4 → V) → P.Adj x y → ¬ (G.Adj v x ∧ G.Adj u y))
    (h6 : ∀ x y z w : V, Function.Injective (![u,v,x,y,z,w] : Fin 6 → V) → P.Adj x y → P.Adj z w → ¬ (G.Adj v y ∧ G.Adj x z ∧ G.Adj u w)) :
    P.Adj a b ∧ ∀ x : V, x ≠ u → x ≠ v → x ≠ a → x ≠ b → ¬ G.Adj v x ∧ ¬ G.Adj a x ∧ ¬ G.Adj b x := by
  classical
  obtain ⟨hM, hS⟩ := hP
  have inj4 : ∀ {p q r s : V}, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      Function.Injective (![p,q,r,s] : Fin 4 → V) := by
    intro p q r s h1 h2 h3 h4 h5 h6 i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have inj6 : ∀ {p q r s t w : V},
      p ≠ q → p ≠ r → p ≠ s → p ≠ t → p ≠ w →
      q ≠ r → q ≠ s → q ≠ t → q ≠ w →
      r ≠ s → r ≠ t → r ≠ w →
      s ≠ t → s ≠ w → t ≠ w →
      Function.Injective (![p,q,r,s,t,w] : Fin 6 → V) := by
    intro p q r s t w h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  let m : V → V := fun x => (hM (hS x)).choose
  have hm : ∀ x, P.Adj x (m x) := fun x => (hM (hS x)).choose_spec.1
  have hm_eq : ∀ x y, P.Adj x y → y = m x := fun x y h => (hM (hS x)).choose_spec.2 y h
  have m_invol : ∀ x, m (m x) = x := fun x => (hm_eq (m x) x (hm x).symm).symm
  have mu : m u = v := (hm_eq u v huv).symm
  have mv : m v = u := (hm_eq v u huv.symm).symm
  have huvG : G.Adj u v := P.adj_sub huv
  have h_uv : u ≠ v := by intro h; rw [h] at huvG; exact G.irrefl huvG
  have hav : a ≠ v := by intro h; apply hua; rw [h]; exact huvG
  have hbv : b ≠ v := by intro h; apply hub; rw [h]; exact huvG
  have hva : G.Adj v a := hsep a hau hua
  have hvb : G.Adj v b := hsep b hbu hub
  have hcu : m a ≠ u := by
    intro h; have hinv := m_invol a; rw [h, mu] at hinv; exact hav hinv.symm
  have hcv : m a ≠ v := by
    intro h; have hinv := m_invol a; rw [h, mv] at hinv; exact hau hinv.symm
  have hca : m a ≠ a := by
    intro h; have hh := hm a; rw [h] at hh; exact G.irrefl (P.adj_sub hh)
  have hnu : ¬ G.Adj u (m a) := by
    intro hAdj
    exact h4 a (m a) (inj4 h_uv hau.symm hcu.symm hav.symm hcv.symm hca.symm) (hm a) ⟨hva, hAdj⟩
  have hma : P.Adj a b := by
    by_contra hcon
    have hmab : m a ≠ b := fun h => hcon (h ▸ hm a)
    rcases honly (m a) hcu hnu with h | h
    · exact hca h
    · exact hmab h
  have hma_b : m a = b := (hm_eq a b hma).symm
  have hmb_a : m b = a := (hm_eq b a hma.symm).symm
  refine ⟨hma, ?_⟩
  intro x hxu hxv hxa hxb
  have hyu : m x ≠ u := by
    intro h; have hinv := m_invol x; rw [h, mu] at hinv; exact hxv hinv.symm
  have hyv : m x ≠ v := by
    intro h; have hinv := m_invol x; rw [h, mv] at hinv; exact hxu hinv.symm
  have hya : m x ≠ a := by
    intro h; have hinv := m_invol x; rw [h, hma_b] at hinv; exact hxb hinv.symm
  have hyb : m x ≠ b := by
    intro h; have hinv := m_invol x; rw [h, hmb_a] at hinv; exact hxa hinv.symm
  have hyx : m x ≠ x := by
    intro h; have hh := hm x; rw [h] at hh; exact G.irrefl (P.adj_sub hh)
  have hnvx : ¬ G.Adj v x := by
    intro hAdj
    have huny : ¬ G.Adj u (m x) :=
      fun huy => h4 x (m x) (inj4 h_uv hxu.symm hyu.symm hxv.symm hyv.symm hyx.symm) (hm x) ⟨hAdj, huy⟩
    rcases honly (m x) hyu huny with h | h
    · exact hya h
    · exact hyb h
  have huy : G.Adj u (m x) := by
    by_contra h
    rcases honly (m x) hyu h with h' | h'
    · exact hya h'
    · exact hyb h'
  have hnax : ¬ G.Adj a x := by
    intro hAdj
    exact h6 a b x (m x)
      (inj6 h_uv hau.symm hbu.symm hxu.symm hyu.symm hav.symm hbv.symm hxv.symm hyv.symm
        hab hxa.symm hya.symm hxb.symm hyb.symm hyx.symm)
      hma (hm x) ⟨hvb, hAdj, huy⟩
  have hnbx : ¬ G.Adj b x := by
    intro hAdj
    exact h6 b a x (m x)
      (inj6 h_uv hbu.symm hau.symm hxu.symm hyu.symm hbv.symm hav.symm hxv.symm hyv.symm
        hab.symm hxb.symm hyb.symm hxa.symm hya.symm hyx.symm)
      hma.symm (hm x) ⟨hva, hAdj, huy⟩
  exact ⟨hnvx, hnax, hnbx⟩
