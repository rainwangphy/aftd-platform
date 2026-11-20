import AFTD.Prelude

/-!
# op874_balanced_trap_enters_only_at_successor

Topic: graphs   Node: 5df501d33cd6

Provenance: helper lemma. Finite balanced cut lemma for the rooted branch reduction.

A trap whose only possible exit is x, with an r→x arc and an entry from x, has no other entering arc. Parallel arcs count separately.
-/

theorem op874_balanced_trap_enters_only_at_successor {X : Type*} [Fintype X] [DecidableEq X] (p q : Equiv.Perm X) (S : Finset X) (r x : X) (hr : r ∉ S) (hx : x ∉ S) (harc : p r = x ∨ q r = x) (hclosed : ∀ u ∈ S, (p u ∈ S ∨ p u = x) ∧ (q u ∈ S ∨ q u = x)) (hentry : ∃ v ∈ S, p x = v ∨ q x = v) : ∀ u, u ∉ S → u ≠ x → p u ∉ S ∧ q u ∉ S := by
  classical
  let f : X × Bool → X × Bool := fun z => (if z.2 then p z.1 else q z.1, z.2)
  have hinj : Function.Injective f := by
    intro ⟨a,ba⟩ ⟨b,bb⟩ h
    cases ba <;> cases bb <;> simp_all [f, Prod.mk.injEq, p.injective.eq_iff, q.injective.eq_iff]
  let W : Finset (X × Bool) := Finset.univ.filter fun z => z.1 ∈ S
  let T := W.image f
  have hcard : T.card = W.card := Finset.card_image_of_injective W hinj
  have hequal : (T \ W).card = (W \ T).card := Finset.card_sdiff_comm hcard
  have hW (z : X × Bool) : z ∈ W ↔ z.1 ∈ S := by simp [W]
  have hT (z : X × Bool) : z ∈ T ↔ ∃ a ∈ W, f a = z := by simp [T]
  have hout (z : X × Bool) (hz : z ∈ T \ W) : z.1 = x := by
    have hzt : z ∈ T := (Finset.mem_sdiff.mp hz).1
    have hzw : z ∉ W := (Finset.mem_sdiff.mp hz).2
    obtain ⟨⟨a, ba⟩, ha, hfa⟩ := (hT z).mp hzt
    have has : a ∈ S := (hW _).mp ha
    cases ba
    · have out : q a ∉ S := by simpa [f, ← hfa, hW] using hzw
      have eq : q a = x := (hclosed a has).2.resolve_left out
      simpa [f, ← hfa] using eq
    · have out : p a ∉ S := by simpa [f, ← hfa, hW] using hzw
      have eq : p a = x := (hclosed a has).1.resolve_left out
      simpa [f, ← hfa] using eq
  have hle : (T \ W).card ≤ 1 := by
    rcases harc with hp | hq
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha1 := hout a ha
      have hb1 := hout b hb
      have hfalse (z : X × Bool) (hz : z ∈ T \ W) : z.2 = false := by
        have ht := (Finset.mem_sdiff.mp hz).1
        obtain ⟨⟨v, bv⟩, hv, he⟩ := (hT z).mp ht
        have vs : v ∈ S := (hW _).mp hv
        cases bv
        · simpa [f, ← he]
        · have pv : p v = x := by simpa [f, ← he] using hout z hz
          have : v = r := p.injective (pv.trans hp.symm)
          subst v
          exact (hr vs).elim
      apply Prod.ext
      · exact ha1.trans hb1.symm
      · rw [hfalse a ha, hfalse b hb]
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha1 := hout a ha
      have hb1 := hout b hb
      have htrue (z : X × Bool) (hz : z ∈ T \ W) : z.2 = true := by
        have ht := (Finset.mem_sdiff.mp hz).1
        obtain ⟨⟨v, bv⟩, hv, he⟩ := (hT z).mp ht
        have vs : v ∈ S := (hW _).mp hv
        cases bv
        · have qv : q v = x := by simpa [f, ← he] using hout z hz
          have : v = r := q.injective (qv.trans hq.symm)
          subst v
          exact (hr vs).elim
        · simpa [f, ← he]
      apply Prod.ext
      · exact ha1.trans hb1.symm
      · rw [htrue a ha, htrue b hb]
  have hinle : (W \ T).card ≤ 1 := by omega
  have hin (u : X) (bu : Bool) (hus : u ∉ S)
      (hres : (f (u,bu)).1 ∈ S) : f (u,bu) ∈ W \ T := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(hW _).mpr hres, ?_⟩
    intro hf
    obtain ⟨a, ha, eq⟩ := (hT _).mp hf
    have : a = (u,bu) := hinj eq
    subst a
    exact hus ((hW _).mp ha)
  obtain ⟨v, hv, hvp | hvq⟩ := hentry
  · have hentry' : f (x,true) ∈ W \ T := hin x true hx (by simpa [f,hvp] using hv)
    intro u hu hux
    constructor
    · intro hup
      have hu' : f (u,true) ∈ W \ T := hin u true hu (by simpa [f] using hup)
      have eq : f (u,true) = f (x,true) := Finset.card_le_one.mp hinle _ hu' _ hentry'
      have : (u,true) = (x,true) := hinj eq
      exact hux (congrArg Prod.fst this)
    · intro huq
      have hu' : f (u,false) ∈ W \ T := hin u false hu (by simpa [f] using huq)
      have eq : f (u,false) = f (x,true) := Finset.card_le_one.mp hinle _ hu' _ hentry'
      have : (u,false) = (x,true) := hinj eq
      exact hux (congrArg Prod.fst this)
  · have hentry' : f (x,false) ∈ W \ T := hin x false hx (by simpa [f,hvq] using hv)
    intro u hu hux
    constructor
    · intro hup
      have hu' : f (u,true) ∈ W \ T := hin u true hu (by simpa [f] using hup)
      have eq : f (u,true) = f (x,false) := Finset.card_le_one.mp hinle _ hu' _ hentry'
      have : (u,true) = (x,false) := hinj eq
      exact hux (congrArg Prod.fst this)
    · intro huq
      have hu' : f (u,false) ∈ W \ T := hin u false hu (by simpa [f] using huq)
      have eq : f (u,false) = f (x,false) := Finset.card_le_one.mp hinle _ hu' _ hentry'
      have : (u,false) = (x,false) := hinj eq
      exact hux (congrArg Prod.fst this)
