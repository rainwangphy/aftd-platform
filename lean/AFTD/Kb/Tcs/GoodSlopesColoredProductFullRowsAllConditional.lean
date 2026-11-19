import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesFiberProductSaturation
import AFTD.Kb.Tcs.GoodSlopesProductDenseRowLevelLines

/-!
# good_slopes_colored_product_full_rows_all_conditional

Topic: combinatorics   Node: f8e45e8fc857

Provenance: helper lemma. Full rows complete the colored product step for OP-1027.

For a colored pq-point set over two finite fields, if at least (p+1)/2 nonzero rows are full, the stated first-field direction classification and fewer colors than first-field points force every unit-coordinate direction to be good.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_colored_product_full_rows_all_conditional
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q r : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q) (hrp : r < p)
    (hdirK : ∀ T : Finset (K × K), T.card = p →
      (∃ G : Finset K, (p+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : K × K => z.2 + a*z.1) T) →
      (∃ x : K, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : K, ∀ z ∈ T, z.2 + a*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (color : ((K × L) × (K × L)) → Fin r)
    (hcard : S.card = p*q)
    (hc : ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 → ∀ u ∈ S, ∀ v ∈ S, color u = color v →
      (u.2.1 + a*u.1.1, u.2.2 + b*u.1.2) = (v.2.1 + a*v.1.1, v.2.2 + b*v.1.2) → u = v)
    (hrows : (p+1)/2 ≤ ((Finset.univ : Finset K).filter fun a => a ≠ 0 ∧
      ∀ b : L, b ≠ 0 → Set.InjOn (fun z : ((K × L) × (K × L)) =>
        (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card) :
    ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 →
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S := by
  classical
  let R : Finset K := Finset.univ.filter fun a => a ≠ 0 ∧ ∀ b : L, b ≠ 0 →
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S
  have hppos : 1 < p := by rw [←hp]; exact Fintype.one_lt_card
  have hn : 0 < (p+1)/2 := Nat.div_pos (by omega) (by decide)
  have hRpos : 0 < R.card := lt_of_lt_of_le hn hrows
  obtain ⟨a0,ha0⟩ := Finset.card_pos.mp hRpos
  have ha0good := (Finset.mem_filter.mp ha0).2.2
  intro a ha b hb
  let F (z : ((K × L) × (K × L))) := z.2.2+b*z.1.2
  let H (z : ((K × L) × (K × L))) := z.2.1+a0*z.1.1
  have hpair : Set.InjOn (fun z => (F z,H z)) S := by
    intro u hu v hv he
    apply ha0good b hb hu hv
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hS : S.card = Fintype.card L * Fintype.card K := by
    simpa [hp,hq,Nat.mul_comm] using hcard
  have hsat := good_slopes_fiber_product_saturation S F H hS hpair
  intro u hu v hv heq
  have hK := congrArg Prod.fst heq
  have hL := congrArg Prod.snd heq
  change u.2.1+a*u.1.1 = v.2.1+a*v.1.1 at hK
  change u.2.2+b*u.1.2 = v.2.2+b*v.1.2 at hL
  let t := F u
  let A := S.filter fun z => F z = t
  have huA : u ∈ A := Finset.mem_filter.mpr ⟨hu,rfl⟩
  have hvA : v ∈ A := Finset.mem_filter.mpr ⟨hv,hL.symm⟩
  have hA : A.card = p := by simpa [A,hp] using (hsat t).1
  let π (z : ((K × L) × (K × L))) : K × K := (z.1.1,z.2.1)
  have hπ : Set.InjOn π A := by
    intro z hz w hw he
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    apply ha0good b hb hz'.1 hw'.1
    apply Prod.ext
    · have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      dsimp [π] at hx hy
      change z.2.1+a0*z.1.1 = w.2.1+a0*w.1.1
      rw [hx,hy]
    · exact hz'.2.trans hw'.2.symm
  let T : Finset (K × K) := A.image π
  have hT : T.card = p := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hπ, hA]
  have hgood : ∀ c ∈ R, Set.InjOn (fun z : K × K => z.2+c*z.1) T := by
    intro c hc z hz w hw he
    have hcgood := (Finset.mem_filter.mp hc).2.2 b hb
    obtain ⟨z,hz0,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w,hw0,rfl⟩ := Finset.mem_image.mp hw
    apply congrArg π
    have hzA := Finset.mem_filter.mp hz0
    have hwA := Finset.mem_filter.mp hw0
    apply hcgood hzA.1 hwA.1
    apply Prod.ext
    · exact he
    · exact hzA.2.trans hwA.2.symm
  have hshape := hdirK T hT ⟨R,hrows,hgood⟩
  rcases hshape with ⟨x,hx⟩ | ⟨d,y,hy⟩
  · have huT : π u ∈ T := Finset.mem_image.mpr ⟨u,huA,rfl⟩
    have hvT : π v ∈ T := Finset.mem_image.mpr ⟨v,hvA,rfl⟩
    have hxuv : u.1.1 = v.1.1 := (hx _ huT).trans (hx _ hvT).symm
    have hyuv : u.2.1 = v.2.1 := by linear_combination hK-a*hxuv
    apply ha0good b hb hu hv
    apply Prod.ext
    · change u.2.1+a0*u.1.1 = v.2.1+a0*v.1.1
      rw [hxuv,hyuv]
    · exact hL
  · by_cases hd : d = 0
    · have huT : π u ∈ T := Finset.mem_image.mpr ⟨u,huA,rfl⟩
      have hvT : π v ∈ T := Finset.mem_image.mpr ⟨v,hvA,rfl⟩
      have huY := hy _ huT
      have hvY := hy _ hvT
      have hyuv : u.2.1 = v.2.1 := by simpa [π,hd] using huY.trans hvY.symm
      have hxuv : u.1.1 = v.1.1 := by
        apply (mul_left_inj' ha).mp
        linear_combination hK-hyuv
      apply ha0good b hb hu hv
      apply Prod.ext
      · change u.2.1+a0*u.1.1 = v.2.1+a0*v.1.1
        rw [hxuv,hyuv]
      · exact hL
    · have hcolor : Set.InjOn color A := by
        intro z hz w hw hc0
        have hz' := Finset.mem_filter.mp hz
        have hw' := Finset.mem_filter.mp hw
        have hzT : π z ∈ T := Finset.mem_image.mpr ⟨z,hz,rfl⟩
        have hwT : π w ∈ T := Finset.mem_image.mpr ⟨w,hw,rfl⟩
        apply hc d hd b hb z hz'.1 w hw'.1 hc0
        apply Prod.ext
        · exact (hy _ hzT).trans (hy _ hwT).symm
        · exact hz'.2.trans hw'.2.symm
      have hle : A.card ≤ r := by
        calc
          A.card = (A.image color).card := (Finset.card_image_of_injOn hcolor).symm
          _ ≤ Fintype.card (Fin r) := Finset.card_le_univ _
          _ = r := Fintype.card_fin r
      omega
