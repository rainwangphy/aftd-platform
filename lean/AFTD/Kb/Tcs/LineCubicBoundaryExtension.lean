import AFTD.Prelude

/-!
# line_cubic_boundary_extension

Topic: quantum   Node: 9f022ffe700a

Provenance: helper lemma. Auxiliary construction for OP-4, the line cubic exact-count question in arXiv:2610.01024; new boundary induction developed here.

Removing the two designated boundary supports, adjoining the new index to every other support and adding four boundary supports preserves the line cubic moment invariant while increasing cardinality by two.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace LineBuild
open Finset

def chi (A y : Finset ℕ) : ZMod 2 := if A ⊆ y then 1 else 0
def moment (S : Finset (Finset ℕ)) (A : Finset ℕ) : ZMod 2 := ∑ y ∈ S, chi A y
def boundary (a b c : ℕ) : Finset (Finset ℕ) := {{a}, {a,b}, {b}, {b,c}}
def step (n : ℕ) (S : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  ((S.erase {n-2}).erase {n-2,n-1}).image (insert n) ∪ boundary (n-2) (n-1) n

structure Good (n : ℕ) (S : Finset (Finset ℕ)) : Prop where
  bounded : ∀ y ∈ S, ∀ i ∈ y, i < n
  nonempty : ∀ y ∈ S, y.Nonempty
  size : S.card = 2*n+1
  left : {n-2} ∈ S
  pair : {n-2,n-1} ∈ S
  right : {n-1} ∉ S
  one : ∀ i < n, moment S {i} = 0
  two : ∀ j < n, ∀ i < j, moment S {i,j} = 0
  three : ∀ k < n, ∀ j < k, ∀ i < j,
    moment S {i,j,k} = if j=i+1 ∧ k=i+2 then 1 else 0

theorem boundary_distinct {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a} : Finset ℕ) ≠ {a,b} ∧ ({a} : Finset ℕ) ≠ {b} ∧
    ({a} : Finset ℕ) ≠ {b,c} ∧ ({a,b} : Finset ℕ) ≠ {b} ∧
    ({a,b} : Finset ℕ) ≠ {b,c} ∧ ({b} : Finset ℕ) ≠ {b,c} := by
  have h1 : ({a} : Finset ℕ) ≠ {a,b} := by
    intro h; have := congrArg Finset.card h; simp [hab] at this
  have h2 : ({a} : Finset ℕ) ≠ {b} := by simpa using hab
  have h3 : ({a} : Finset ℕ) ≠ {b,c} := by
    intro h; have := congrArg Finset.card h; simp [hbc] at this
  have h4 : ({a,b} : Finset ℕ) ≠ {b} := by
    intro h; have := congrArg Finset.card h; simp [hab] at this
  have h5 : ({a,b} : Finset ℕ) ≠ {b,c} := by
    intro h
    have hh : a ∈ ({b,c} : Finset ℕ) := h ▸ (by simp)
    simpa [hab, hac] using hh
  have h6 : ({b} : Finset ℕ) ≠ {b,c} := by
    intro h; have := congrArg Finset.card h; simp [hbc] at this
  exact ⟨h1,h2,h3,h4,h5,h6⟩

theorem structural (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset ℕ)) (h : Good n S) :
    (∀ y ∈ step n S, ∀ i ∈ y, i < n+1) ∧
    (∀ y ∈ step n S, y.Nonempty) ∧ (step n S).card = 2*(n+1)+1 ∧
    {n-1} ∈ step n S ∧ {n-1,n} ∈ step n S ∧ {n} ∉ step n S ∧
    (∀ f : Finset ℕ → ZMod 2,
      (∑ y ∈ step n S, f y) = (∑ y ∈ S, f (insert n y)) -
        f {n-2,n} - f {n-2,n-1,n} + f {n-2} + f {n-2,n-1} + f {n-1} + f {n-1,n}) := by
  classical
  let a := n-2
  let b := n-1
  let T := (S.erase {a}).erase {a,b}
  have hab : a ≠ b := by dsimp [a,b]; omega
  have han : a ≠ n := by dsimp [a]; omega
  have hbn : b ≠ n := by dsimp [b]; omega
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := boundary_distinct hab han hbn
  have hTS : T ⊆ S := fun y hy => (mem_erase.mp (mem_erase.mp hy).2).2
  have hnc (y) (hy : y ∈ S) : n ∉ y := by
    intro hm; have := h.bounded y hy n hm; omega
  have hinj : Set.InjOn (insert n) (↑T : Set (Finset ℕ)) := by
    intro x hx y hy he
    have hh := congrArg (erase · n) he
    simpa [hnc x (hTS hx), hnc y (hTS hy)] using hh
  have hdisj : Disjoint (T.image (insert n)) (boundary a b n) := by
    apply disjoint_left.mpr
    intro z hz hr
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    have hmem : n ∈ insert n y := mem_insert_self _ _
    simp only [boundary, mem_insert, mem_singleton] at hr
    rcases hr with hr | hr | hr | hr
    · rw [hr] at hmem; simpa [Ne.symm han] using hmem
    · rw [hr] at hmem; simpa [Ne.symm han, Ne.symm hbn] using hmem
    · rw [hr] at hmem; simpa [Ne.symm hbn] using hmem
    · have hh := congrArg (erase · n) hr
      have hbr : ({b,n} : Finset ℕ).erase n = {b} := by ext i; simp; omega
      have he : y = {b} := by simpa only [erase_insert (hnc y (hTS hy)), hbr] using hh
      exact h.right (he ▸ hTS hy)
  have habmem : ({a,b} : Finset ℕ) ∈ S.erase {a} := by
    exact mem_erase.mpr ⟨Ne.symm h1, h.pair⟩
  have hTcard : T.card = S.card - 2 := by
    dsimp [T]
    rw [card_erase_of_mem habmem, card_erase_of_mem h.left]
    omega
  have hRcard : (boundary a b n).card = 4 := by
    simp [boundary, h1,h2,h3,h4,h5,h6]
  have he : step n S = T.image (insert n) ∪ boundary a b n := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy i hi
    rw [he] at hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      rcases mem_insert.mp hi with rfl | hi
      · omega
      · have := h.bounded z (hTS hz) i hi; omega
    · simp only [boundary, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mem_insert, mem_singleton] at hi <;> dsimp [a,b] at * <;> omega
  · intro y hy
    rw [he] at hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      exact ⟨n, by simp⟩
    · simp only [boundary, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp
  · rw [he, card_union_of_disjoint hdisj, card_image_of_injOn hinj, hTcard, hRcard, h.size]
    omega
  · rw [he]; simp [boundary, b]
  · rw [he]; simp [boundary, b]
  · intro hm
    rw [he] at hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨y,hy,heq⟩ := mem_image.mp hm
      have hh := congrArg (erase · n) heq
      have hempty : y = ∅ := by simpa [hnc y (hTS hy)] using hh
      exact (h.nonempty y (hTS hy)).ne_empty hempty
    · simp only [boundary, mem_insert, mem_singleton] at hm
      rcases hm with hm | hm | hm | hm
      · have hh := congrArg (fun z : Finset ℕ => n ∈ z) hm
        simp [Ne.symm han] at hh
      · have hh := congrArg (fun z : Finset ℕ => n ∈ z) hm
        simp [Ne.symm han, Ne.symm hbn] at hh
      · have hh := congrArg (fun z : Finset ℕ => n ∈ z) hm
        simp [Ne.symm hbn] at hh
      · have hh := congrArg (fun z : Finset ℕ => b ∈ z) hm
        simp [hbn] at hh
  · intro f
    rw [he, sum_union hdisj, sum_image hinj]
    have e1 := sum_erase_add (s := S) (f := fun y => f (insert n y)) h.left
    have e2 := sum_erase_add (s := S.erase {a}) (f := fun y => f (insert n y)) habmem
    change (∑ y ∈ T, f (insert n y)) + _ = _
    rw [← e1, ← e2]
    simp only [boundary, sum_insert, mem_insert, mem_singleton, h1,h2,h3,h4,h5,h6,
      not_false_eq_true, sum_singleton]
    have e3 : insert n ({a} : Finset ℕ) = {a,n} := by ext i; simp; tauto
    have e4 : insert n ({a,b} : Finset ℕ) = {a,b,n} := by ext i; simp; tauto
    dsimp only [a,b] at e3 e4
    rw [e3,e4]
    dsimp only [a,b] at *
    simp [boundary, h1,h2,h3,h4,h5,h6]
    ring

theorem chi_insert_old (A y : Finset ℕ) (c : ℕ) (h : c ∉ A) :
    chi A (insert c y) = chi A y := by
  unfold chi
  congr 1
  apply propext
  constructor
  · intro hs i hi
    rcases mem_insert.mp (hs hi) with he | he
    · exact False.elim (h (he ▸ hi))
    · exact he
  · exact fun hs i hi => mem_insert_of_mem (hs hi)

theorem chi_insert_new (B y : Finset ℕ) (c : ℕ) (h : c ∉ B) :
    chi (insert c B) (insert c y) = chi B y := by
  unfold chi
  have he : insert c B ⊆ insert c y ↔ B ⊆ y := by
    rw [insert_subset_iff]
    simp only [mem_insert_self, true_and]
    constructor
    · intro hs i hi
      rcases mem_insert.mp (hs hi) with he | he
      · exact False.elim (h (he ▸ hi))
      · exact he
    · exact fun hs i hi => mem_insert_of_mem (hs hi)
  simp only [he]

theorem moment_old (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset ℕ))
    (h : Good n S) (A : Finset ℕ) (hc : n ∉ A) :
    moment (step n S) A = moment S A := by
  have hs := (structural n hn S h).2.2.2.2.2.2 (chi A)
  change moment (step n S) A = _ at hs
  simp only [chi_insert_old A _ n hc] at hs
  have h1 : chi A {n-2,n} = chi A {n-2} := by
    rw [Finset.pair_comm]; exact chi_insert_old A {n-2} n hc
  have h2 : chi A {n-2,n-1,n} = chi A {n-2,n-1} := by
    have he : ({n-2,n-1,n} : Finset ℕ) = insert n {n-2,n-1} := by ext i; simp; tauto
    rw [he]; exact chi_insert_old A {n-2,n-1} n hc
  have h3 : chi A {n-1,n} = chi A {n-1} := by
    rw [Finset.pair_comm]; exact chi_insert_old A {n-1} n hc
  rw [h1,h2,h3] at hs
  change moment (step n S) A = moment S A
  rw [hs]
  change moment S A - _ - _ + _ + _ + _ + _ = moment S A
  have hz : (2 : ZMod 2) = 0 := by decide
  linear_combination hz * chi A {n-1}

theorem moment_new (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset ℕ))
    (h : Good n S) (B : Finset ℕ) (hc : n ∉ B) :
    moment (step n S) (insert n B) = moment S B - chi B {n-2} -
      chi B {n-2,n-1} + chi B {n-1} := by
  have hs := (structural n hn S h).2.2.2.2.2.2 (chi (insert n B))
  change moment (step n S) (insert n B) = _ at hs
  simp only [chi_insert_new B _ n hc] at hs
  have hzero (y : Finset ℕ) (hy : n ∉ y) : chi (insert n B) y = 0 := by
    unfold chi
    rw [if_neg]
    exact fun hh => hy (hh (mem_insert_self _ _))
  have ha : n ∉ ({n-2} : Finset ℕ) := by simp; omega
  have hab : n ∉ ({n-2,n-1} : Finset ℕ) := by simp; omega
  have hb : n ∉ ({n-1} : Finset ℕ) := by simp; omega
  rw [hzero _ ha, hzero _ hab, hzero _ hb] at hs
  have e1 : chi (insert n B) {n-2,n} = chi B {n-2} := by
    rw [Finset.pair_comm]; exact chi_insert_new B {n-2} n hc
  have e2 : chi (insert n B) {n-2,n-1,n} = chi B {n-2,n-1} := by
    have he : ({n-2,n-1,n} : Finset ℕ) = insert n {n-2,n-1} := by ext i; simp; tauto
    rw [he]; exact chi_insert_new B {n-2,n-1} n hc
  have e3 : chi (insert n B) {n-1,n} = chi B {n-1} := by
    rw [Finset.pair_comm]; exact chi_insert_new B {n-1} n hc
  simpa only [e1,e2,e3,add_zero, moment] using hs


theorem good_step (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset ℕ))
    (h : Good n S) : Good (n+1) (step n S) := by
  obtain ⟨hb,he,hc,hl,hp,hr,hs⟩ := structural n hn S h
  have e1 : n+1-2 = n-1 := by omega
  have e2 : n+1-1 = n := by omega
  refine ⟨hb,he,hc,?_,?_,?_,?_,?_,?_⟩
  · simpa only [e1] using hl
  · simpa only [e1,e2] using hp
  · simpa only [e2] using hr
  · intro i hi
    by_cases hin : i < n
    · rw [moment_old n hn S h {i} (by simp; omega)]
      exact h.one i hin
    · have ei : i = n := by omega
      subst i
      have hm := moment_new n hn S h ∅ (by simp)
      have ht : (2 : ZMod 2) = 0 := by decide
      have hz : moment S ∅ = 1 := by
        simp [moment, chi, h.size, Nat.cast_add, Nat.cast_mul, ht]
      simpa [hz, chi, show (1 : ZMod 2)+1=0 by decide] using hm
  · intro j hj i hi
    by_cases hjn : j < n
    · rw [moment_old n hn S h {i,j} (by simp; omega)]
      exact h.two j hjn i hi
    · have ej : j = n := by omega
      subst j
      have hm := moment_new n hn S h {i} (by simp; omega)
      have ee : ({i,n} : Finset ℕ) = insert n {i} := by ext x; simp; tauto
      rw [ee, hm, h.one i hi]
      simp only [chi, singleton_subset_iff, mem_insert, mem_singleton]
      split_ifs <;> first | decide | omega
  · intro k hk j hj i hi
    by_cases hkn : k < n
    · rw [moment_old n hn S h {i,j,k} (by simp; omega)]
      exact h.three k hkn j hj i hi
    · have ek : k = n := by omega
      subst k
      have hm := moment_new n hn S h {i,j} (by simp; omega)
      have ee : ({i,j,n} : Finset ℕ) = insert n {i,j} := by ext x; simp; tauto
      rw [ee, hm, h.two j hj i hi]
      simp only [chi, insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton]
      split_ifs <;> first | decide | omega

end LineBuild

theorem line_cubic_boundary_extension (n : ℕ) (hn : 5 ≤ n) (S : Finset (Finset ℕ)) (h : LineBuild.Good n S) : LineBuild.Good (n+1) (LineBuild.step n S) := by
  exact LineBuild.good_step n hn S h
