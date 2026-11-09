import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SymB
import AFTD.Kb.Tcs.G

/-!
# exists_physical_pairs_bijective

Topic: quantum   Node: b507d99ada8a

Provenance: helper lemma. arXiv:2610.04621 Lemma 5 (Appendix B)

Let L be a 2l-dimensional submodule of V k 2 over F 2 that is nondegenerate under the symplectic bilinear form symB. Then there exists a subset S of Fin k of cardinality l such that the projection map v ↦ (v.1|_S, v.2|_S) is a bijection from L to Set.univ.
-/

open Module in
lemma r6AltEven {K : Type} [Field K] : ∀ (n : ℕ) (E : Type) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E), (∀ u, B u u = 0) → (∀ u, (∀ v, B u v = 0) → u = 0) →
    finrank K E = n → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ B hA hN hn
    by_cases hn0 : n = 0
    · subst hn0; exact Even.zero
    have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (hN v h)
    have hskew : ∀ a b, B a b = - B b a := by
      intro a b
      have e : B (a + b) (a + b) = B a a + B a b + B b a + B b b := by
        simp only [map_add, LinearMap.add_apply]; ring
      linear_combination hA (a + b) - hA a - hA b - e
    set c := B v w with hc
    let g : E →ₗ[K] K × K := (B.flip v).prod (B.flip w)
    have hg : ∀ u, g u = (B u v, B u w) := fun u => rfl
    have hgs : Function.Surjective g := by
      rintro ⟨a, b⟩
      refine ⟨(b / c) • v + (-a / c) • w, ?_⟩
      rw [hg]
      have hwv : B w v = -c := by rw [hskew w v]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hA, smul_eq_mul, hwv]
      ext
      · simp only [mul_zero, zero_add]; field_simp
      · simp only [mul_zero, add_zero, ← hc]; field_simp
    have hrn := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hgs, finrank_top, Module.finrank_prod, Module.finrank_self, hn] at hrn
    have hker : finrank K (LinearMap.ker g) < n := by omega
    have hC : Even (finrank K (LinearMap.ker g)) := by
      refine ih _ hker (LinearMap.ker g) (B.restrict _) (fun u => hA _) ?_ rfl
      intro y hy
      apply Subtype.ext
      show (y : E) = 0
      apply hN
      intro z
      have hyv : B y v = 0 := by have := y.2; rw [LinearMap.mem_ker, hg] at this; exact (Prod.ext_iff.mp this).1
      have hyw : B y w = 0 := by have := y.2; rw [LinearMap.mem_ker, hg] at this; exact (Prod.ext_iff.mp this).2
      have hcz : c ≠ 0 := hw
      have hwv : B w v = -c := by rw [hskew w v]
      have hvw : B v w = c := rfl
      have hz' : z - (B z w / c) • v - (-B z v / c) • w ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker, hg, Prod.mk_eq_zero]
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hA, smul_eq_mul, hwv, hvw, mul_zero, sub_zero]
        constructor
        · field_simp; ring
        · field_simp; ring
      have h : B y (z - (B z w / c) • v - (-B z v / c) • w) = 0 := hy ⟨_, hz'⟩
      simp only [map_sub, map_smul, hyv, hyw, smul_eq_mul, mul_zero, sub_zero] at h
      exact h
    obtain ⟨m, hm⟩ := hC
    exact ⟨m + 1, by omega⟩

open Module in
theorem r6Main {K : Type} [Field K] {ι : Type} [DecidableEq ι] (I : Finset ι) :
    ∀ (E : Type) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
      (x z : ι → Module.Dual K E) (l : ℕ), finrank K E = 2 * l →
      (∀ u, (∀ v, ∑ i ∈ I, (x i u * z i v - z i u * x i v) = 0) → u = 0) →
      ∃ S ⊆ I, S.card = l ∧ ∀ u : E, (∀ s ∈ S, x s u = 0 ∧ z s u = 0) → u = 0 := by
  induction I using Finset.induction_on with
  | empty =>
    intro E _ _ _ x z l hl hN
    have hall : ∀ u : E, u = 0 := fun u => hN u (fun v => by simp)
    have hE : Subsingleton E := ⟨fun a b => by rw [hall a, hall b]⟩
    have hfr : finrank K E = 0 := finrank_zero_of_subsingleton
    refine ⟨∅, le_refl _, ?_, fun u _ => hall u⟩
    simp; omega
  | insert a I ha ih =>
    intro E _ _ _ x z l hl hN
    let B : LinearMap.BilinForm K E := LinearMap.mk₂ K
      (fun u v => ∑ i ∈ I, (x i u * z i v - z i u * x i v))
      (by intro u u' v; simp only [map_add]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring)
      (by intro c u v; simp only [map_smul, smul_eq_mul]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring)
      (by intro u v v'; simp only [map_add]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring)
      (by intro c u v; simp only [map_smul, smul_eq_mul]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring)
    have hB : ∀ u v, B u v = ∑ i ∈ I, (x i u * z i v - z i u * x i v) := fun u v => rfl
    have hA : ∀ u, B u u = 0 := by
      intro u; rw [hB]; refine Finset.sum_eq_zero fun i _ => ?_; ring
    have hskew : ∀ a b, B a b = - B b a := by
      intro u v; rw [hB, hB, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    let R : Submodule K E := LinearMap.ker B
    have hmemR : ∀ u, u ∈ R ↔ ∀ v, B u v = 0 := by
      intro u
      show B u = 0 ↔ _
      constructor
      · intro h v; rw [h]; rfl
      · intro h; ext v; exact h v
    by_cases hR : R = ⊥
    · have hN' : ∀ u, (∀ v, ∑ i ∈ I, (x i u * z i v - z i u * x i v) = 0) → u = 0 := by
        intro u hu
        have : u ∈ R := (hmemR u).mpr (fun v => by rw [hB]; exact hu v)
        rw [hR] at this
        exact (Submodule.mem_bot K).mp this
      obtain ⟨S, hS, hc, hu⟩ := ih E x z l hl hN'
      exact ⟨S, hS.trans (Finset.subset_insert _ _), hc, hu⟩
    · let f : E →ₗ[K] K × K := (x a).prod (z a)
      have hf : ∀ u, f u = (x a u, z a u) := fun u => rfl
      have hinj : ∀ u ∈ R, f u = 0 → u = 0 := by
        intro u hu hfu
        have h1 : x a u = 0 := (Prod.ext_iff.mp hfu).1
        have h2 : z a u = 0 := (Prod.ext_iff.mp hfu).2
        apply hN
        intro v
        rw [Finset.sum_insert ha, h1, h2, zero_mul, zero_mul, sub_zero, zero_add]
        rw [← hB]
        exact (hmemR u).mp hu v
      -- parity of the radical
      obtain ⟨C, hC⟩ := Submodule.exists_isCompl R
      have hCeven : Even (finrank K C) := by
        refine r6AltEven (K := K) _ C (B.restrict C) (fun u => hA _) ?_ rfl
        intro y hy
        apply Subtype.ext
        show (y : E) = 0
        have hyall : ∀ v, B y v = 0 := by
          intro v
          have hv : v ∈ R ⊔ C := by rw [hC.sup_eq_top]; trivial
          obtain ⟨r, hr, c, hc', rfl⟩ := Submodule.mem_sup.mp hv
          have h1 : B y r = 0 := by rw [hskew]; rw [(hmemR r).mp hr y]; simp
          have h2 : B y c = 0 := hy ⟨c, hc'⟩
          rw [map_add, h1, h2, zero_add]
        have hyR : (y : E) ∈ R := (hmemR _).mpr hyall
        have := hC.disjoint.le_bot ⟨hyR, y.2⟩
        exact (Submodule.mem_bot K).mp this
      have hfrsum := Submodule.finrank_add_eq_of_isCompl hC
      have hle2 : finrank K R ≤ 2 := by
        have hinj' : Function.Injective (f.comp R.subtype) := by
          rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
          intro u hu
          exact Subtype.ext (hinj u.1 u.2 hu)
        have := LinearMap.finrank_le_finrank_of_injective hinj'
        simpa [Module.finrank_prod] using this
      have hpos : 0 < finrank K R := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hR
      have hR2 : finrank K R = 2 := by
        obtain ⟨m, hm⟩ := hCeven
        omega
      have hsurjR : Function.Surjective (f.comp R.subtype) := by
        have hinj' : Function.Injective (f.comp R.subtype) := by
          rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
          intro u hu
          exact Subtype.ext (hinj u.1 u.2 hu)
        exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (by simp [Module.finrank_prod, hR2])).mp hinj'
      obtain ⟨u1, hu1⟩ := hsurjR (1, 0)
      obtain ⟨u2, hu2⟩ := hsurjR (0, 1)
      have hu1' : f u1.1 = (1, 0) := hu1
      have hu2' : f u2.1 = (0, 1) := hu2
      have hfs : Function.Surjective f := by
        rintro ⟨p, q⟩
        refine ⟨p • u1.1 + q • u2.1, ?_⟩
        rw [map_add, map_smul, map_smul, hu1', hu2']
        ext <;> simp
      have hrn := LinearMap.finrank_range_add_finrank_ker f
      rw [LinearMap.range_eq_top.mpr hfs, finrank_top, Module.finrank_prod, Module.finrank_self, hl] at hrn
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hE' : finrank K (LinearMap.ker f) = 2 * l' := by omega
      let x' : ι → Module.Dual K (LinearMap.ker f) := fun i => (x i).comp (LinearMap.ker f).subtype
      let z' : ι → Module.Dual K (LinearMap.ker f) := fun i => (z i).comp (LinearMap.ker f).subtype
      have hN' : ∀ u : LinearMap.ker f,
          (∀ v, ∑ i ∈ I, (x' i u * z' i v - z' i u * x' i v) = 0) → u = 0 := by
        intro w hw
        apply Subtype.ext
        show (w : E) = 0
        apply hinj _ _ w.2
        apply (hmemR _).mpr
        intro v
        have hx1 : x a u1.1 = 1 := (Prod.ext_iff.mp hu1').1
        have hz1 : z a u1.1 = 0 := (Prod.ext_iff.mp hu1').2
        have hx2 : x a u2.1 = 0 := (Prod.ext_iff.mp hu2').1
        have hz2 : z a u2.1 = 1 := (Prod.ext_iff.mp hu2').2
        have hv' : v - (x a v) • u1.1 - (z a v) • u2.1 ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf]
          simp only [map_sub, map_smul, smul_eq_mul, hx1, hz1, hx2, hz2, mul_one, mul_zero, sub_zero, sub_self]
          rfl
        have h1 : B w.1 u1.1 = 0 := by rw [hskew, (hmemR _).mp u1.2 w.1]; simp
        have h2 : B w.1 u2.1 = 0 := by rw [hskew, (hmemR _).mp u2.2 w.1]; simp
        have h3 := hw ⟨_, hv'⟩
        have h4 : B w.1 (v - (x a v) • u1.1 - (z a v) • u2.1) = 0 := by
          rw [hB]; exact h3
        simpa [map_sub, map_smul, h1, h2] using h4
      obtain ⟨S, hS, hc, hu⟩ := ih (LinearMap.ker f) x' z' l' hE' hN'
      refine ⟨insert a S, Finset.insert_subset_insert a hS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun h => ha (hS h)), hc]
      · intro u hzero
        have h1 := hzero a (Finset.mem_insert_self a S)
        have hker : u ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf]; exact Prod.ext h1.1 h1.2
        have h2 : (⟨u, hker⟩ : LinearMap.ker f) = 0 := by
          apply hu
          intro s hs
          exact hzero s (Finset.mem_insert_of_mem hs)
        exact congrArg Subtype.val h2

/-- Existence of a subset of physical coordinate pairs on which projection is bijective on a nondegenerate symplectic subspace. -/
lemma exists_physical_pairs_bijective {k l : ℕ} (L : Submodule (F 2) (V k 2))
    (hdim : Module.finrank (F 2) L = 2 * l)
    (hnondeg : (symB.restrict L).Nondegenerate) :
    ∃ S : Finset (Fin k), S.card = l ∧
      Set.BijOn (fun v : V k 2 => ((fun (s : S) => v.1 s.1), (fun (s : S) => v.2 s.1))) (L : Set (V k 2)) Set.univ := by
  classical
  let x : Fin k → Module.Dual (F 2) L := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst (F 2) _ _).comp L.subtype)
  let z : Fin k → Module.Dual (F 2) L := fun i =>
    (LinearMap.proj i).comp ((LinearMap.snd (F 2) _ _).comp L.subtype)
  have hN : ∀ u : L, (∀ v : L, ∑ i ∈ (Finset.univ : Finset (Fin k)), (x i u * z i v - z i u * x i v) = 0) → u = 0 := by
    intro u hu
    exact hnondeg.1 u (fun v => hu v)
  obtain ⟨S, -, hc, hS⟩ := r6Main (K := F 2) (Finset.univ : Finset (Fin k)) (L) x z l hdim hN
  refine ⟨S, hc, ?_⟩
  let φ : L →ₗ[F 2] (S → F 2) × (S → F 2) :=
    (LinearMap.pi fun s : S => x s.1).prod (LinearMap.pi fun s : S => z s.1)
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hS
    intro s hs
    exact ⟨congrFun (Prod.ext_iff.mp hu).1 ⟨s, hs⟩, congrFun (Prod.ext_iff.mp hu).2 ⟨s, hs⟩⟩
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, hdim, hc, two_mul])).mp hφinj
  refine ⟨?_, ?_, ?_⟩
  · intro v _; exact Set.mem_univ _
  · intro v hv w hw hvw
    have : φ ⟨v, hv⟩ = φ ⟨w, hw⟩ := hvw
    exact congrArg Subtype.val (hφinj this)
  · intro y _
    obtain ⟨u, hu⟩ := hφsurj y
    exact ⟨u.1, u.2, hu⟩
