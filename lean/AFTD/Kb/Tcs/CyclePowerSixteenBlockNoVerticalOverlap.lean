import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockOverlapStabilizes
import AFTD.Kb.Tcs.CyclePowerEightBlockActiveRetainedHalves
import AFTD.Kb.Tcs.CyclePowerEightBlockActiveRootSeparation
import AFTD.Kb.Tcs.CyclePowerEightBlockDoubleGapTransfer
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerEightBlockStableOverlap

/-!
# cycle_power_sixteen_block_no_vertical_overlap

Topic: combinatorics   Node: b07b67514218

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635. The main covering theorem and vertical-defect exclusion remain open. Experiments8048/8049 suggested the two ordinary distances; the proof is uniform in h and uses Lean only. No advance flag.

For any positive h and Boolean rooted model of radius16h satisfying the explicit Geometry hypotheses (selected endpoints, three parent matchings, exact12h/14h/15h ownership, monotone outer eighths, full ordinary coverage), suppose globally every selected C_t at offset2h+t also selects A_t at offset t. Then no root can select A_t,C_t while missing A_s with t<s<2h.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace CyclePowerSixteenBlock
structure Geometry (h : ℕ) (x : ℤ → ℕ → Bool) : Prop where
  pos : 0 < h
  ends : ∀ p, x p 0 = true ∧ x p (16*h-1) = true
  lowMono : ∀ p a b, a ≤ b → b < 2*h → x p b = true → x p a = true
  highMono : ∀ p a b, 14*h ≤ a → a ≤ b → b < 16*h → x p a = true → x p b = true
  parent4 : ∀ p a, a < 8*h →
    (a < 4*h → x p (a+8*h) = true → x p a = true) ∧
    (4*h ≤ a → x p a = true → x p (a+8*h) = true)
  parent6 : ∀ p a, a < 4*h →
    (a < 2*h → x p (a+12*h) = true → x p a = true) ∧
    (2*h ≤ a → x p a = true → x p (a+12*h) = true)
  parent7 : ∀ p a, a < 2*h →
    (a < h → x p (a+14*h) = true → x p a = true) ∧
    (h ≤ a → x p a = true → x p (a+14*h) = true)
  exact6 : ∀ v : ℤ, (range (4*h)).sum (fun a =>
    (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+12*h)).toNat) = 1
  exact7 : ∀ v : ℤ, (range (2*h)).sum (fun a =>
    (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+14*h)).toNat) = 1
  exact15 : ∀ v : ℤ, (range h).sum (fun a =>
    (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+15*h)).toNat) = 1
  cover : ∀ d : ℕ, 1 ≤ d → d < 16*h → ∀ v : ℤ,
    ∃ a : ℕ, a < 16*h-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true

def Active (h : ℕ) (x : ℤ → ℕ → Bool) (p : ℤ) : Prop :=
  ∃ t < 2*h, x p t = true ∧ x p (14*h+t) = true

def Canonical (h : ℕ) (x : ℤ → ℕ → Bool) (p : ℤ) : Prop :=
  x p (h-1) = true ∧ x p (3*h-1) = true ∧ x p (2*h-1) = false

variable {h : ℕ} {x : ℤ → ℕ → Bool}

lemma Geometry.childZ (M : Geometry h x) (p : ℤ) (a : ℕ) (ha : a < 2*h)
    (hc : x p (2*h+a) = true) : x p (14*h+a) = true := by
  have hh := (M.parent6 p (2*h+a) (by omega)).2 (by omega) hc
  convert hh using 1 <;> congr 1 <;> omega

lemma Geometry.fullRetained (M : Geometry h x) {p : ℤ} (hp : Active h x p) :
    ∀ a < h, x p a = true ∧ x p (15*h+a) = true := by
  obtain ⟨t,ht,hA,hB⟩ := hp
  exact cycle_power_eight_block_active_retained_halves h x M.parent7
    (fun p => ⟨M.lowMono p,M.highMono p⟩) p t ht hA hB

lemma Geometry.sep (M : Geometry h x) {p r : ℤ} (hpr : p < r)
    (hp : Active h x p) (hr : Active h x r) : (h : ℤ) ≤ r-p := by
  obtain ⟨t,ht,hpA,hpB⟩ := hp
  obtain ⟨u,hu,hrA,hrB⟩ := hr
  let d := (r-p).toNat
  have hd : r=p+(d : ℤ) := by dsimp [d]; omega
  have hs := cycle_power_eight_block_active_root_separation h M.pos x M.parent7
    (fun p => ⟨M.lowMono p,M.highMono p⟩) M.exact15 p d t u (by dsimp [d]; omega) ht hu hpA hpB
    (by simpa only [← hd] using hrA) (by simpa only [← hd] using hrB)
  omega

lemma Geometry.own6 (M : Geometry h x) (p r : ℤ) (a b : ℕ) (ha : a < 4*h) (hb : b < 4*h)
    (he : p+(a : ℤ)=r+(b : ℤ))
    (hpa : x p a = true) (hpa' : x p (a+12*h) = true)
    (hrb : x r b = true) (hrb' : x r (b+12*h) = true) : p=r := by
  have hex : ∀ v : ℤ, (range (4*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-4*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-4*h=a+12*h := by omega
    simpa only [hi] using M.exact6 v
  have hu := cycle_power_exact_pair_unique (16*h) (4*h) x hex (p+(a : ℤ)) a b ha hb
    (by simpa using hpa)
    (by simpa only [add_sub_cancel_right,show a+16*h-4*h=a+12*h by omega] using hpa')
    (by convert hrb using 1 <;> congr 1 <;> omega)
    (by convert hrb' using 1 <;> congr 1 <;> omega)
  omega

lemma Geometry.own7 (M : Geometry h x) (p r : ℤ) (a b : ℕ) (ha : a < 2*h) (hb : b < 2*h)
    (he : p+(a : ℤ)=r+(b : ℤ))
    (hpa : x p a = true) (hpa' : x p (a+14*h) = true)
    (hrb : x r b = true) (hrb' : x r (b+14*h) = true) : p=r := by
  have hex : ∀ v : ℤ, (range (2*h)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+16*h-2*h)).toNat) = 1 := by
    intro v
    have hi (a : ℕ) : a+16*h-2*h=a+14*h := by omega
    simpa only [hi] using M.exact7 v
  have hu := cycle_power_exact_pair_unique (16*h) (2*h) x hex (p+(a : ℤ)) a b ha hb
    (by simpa using hpa)
    (by simpa only [add_sub_cancel_right,show a+16*h-2*h=a+14*h by omega] using hpa')
    (by convert hrb using 1 <;> congr 1 <;> omega)
    (by convert hrb' using 1 <;> congr 1 <;> omega)
  omega

lemma Geometry.grid (M : Geometry h x) (p r : ℤ) (hr : Active h x r)
    (h0 : Active h x p) (h1 : Active h x (p-(h : ℤ))) (h2 : Active h x (p-(2*h : ℕ)))
    (hl : p-(3*h : ℕ) < r) (hu : r < p+(h : ℤ)) :
    r=p ∨ r=p-(h : ℤ) ∨ r=p-(2*h : ℕ) := by
  have cmp (a : ℤ) (ha : Active h x a) : r=a ∨ r+(h : ℤ) ≤ a ∨ a+(h : ℤ) ≤ r := by
    rcases lt_trichotomy r a with hlt | he | hgt
    · have hs := M.sep hlt hr ha
      omega
    · exact Or.inl he
    · have hs := M.sep hgt ha hr
      omega
  have hc0 := cmp p h0
  have hc1 := cmp (p-(h : ℤ)) h1
  have hc2 := cmp (p-(2*h : ℕ)) h2
  push_cast at *
  omega

lemma Geometry.cover13Active (M : Geometry h x) (v : ℤ) :
    ∃ a < 3*h, x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+13*h) = true ∧
      Active h x (v-(a : ℤ)) := by
  obtain ⟨a,ha,hA,hB⟩ := M.cover (13*h) (by have := M.pos; omega) (by have := M.pos; omega) v
  have ha3 : a < 3*h := by omega
  refine ⟨a,ha3,hA,hB,?_⟩
  let p := v-(a : ℤ)
  by_cases ha1 : a < h
  · have hh : x p (h+a) = true := by
      apply (M.parent6 p (h+a) (by omega)).1 (by omega)
      convert hB using 1 <;> congr 1 <;> omega
    have hz := (M.parent7 p (h+a) (by omega)).2 (by omega) hh
    exact ⟨h+a,by omega,hh,by convert hz using 1 <;> congr 1 <;> omega⟩
  · by_cases ha2 : a < 2*h
    · refine ⟨a,ha2,hA,?_⟩
      apply M.highMono p (a+13*h) (14*h+a) (by omega) (by omega) (by omega)
      exact hB
    · let b := a-2*h
      have hb : b < h := by dsimp [b]; omega
      have hc : x p (2*h+b) = true := by convert hA using 1 <;> congr 1 <;> dsimp [b] <;> omega
      have hz := M.childZ p b (by omega) hc
      have ha' := (M.parent7 p b (by omega)).1 hb (by convert hz using 1 <;> congr 1 <;> omega)
      exact ⟨b,by omega,ha',hz⟩

lemma Geometry.canonicalActive (M : Geometry h x) {p : ℤ} (hp : Canonical h x p) : Active h x p := by
  have hc : x p (2*h+(h-1)) = true := by convert hp.2.1 using 1 <;> congr 1 <;> have := M.pos <;> omega
  exact ⟨h-1,by have := M.pos; omega,hp.1,M.childZ p (h-1) (by have := M.pos; omega) hc⟩

lemma Geometry.missLast (M : Geometry h x) {p : ℤ} {a : ℕ} (ha : a < 2*h) (hm : x p a = false) :
    x p (2*h-1) = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hh := M.lowMono p a (2*h-1) (by omega) (by have := M.pos; omega) hc
  rw [hm] at hh
  contradiction

lemma Geometry.maxChildOfThree (M : Geometry h x) (p : ℤ)
    (h0 : Active h x p) (h1 : Active h x (p-(h : ℤ))) (h2 : Active h x (p-(2*h : ℕ)))
    (m0 : x p (2*h-1) = false) (m1 : x (p-(h : ℤ)) (2*h-1) = false)
    (m2 : x (p-(2*h : ℕ)) (2*h-1) = false) : Canonical h x (p-(2*h : ℕ)) := by
  obtain ⟨a,ha,hA,hB,hact⟩ := M.cover13Active (p+(h : ℤ)-1)
  have hg := M.grid p (p+(h : ℤ)-1-(a : ℤ)) hact h0 h1 h2
    (by have := M.pos; omega) (by omega)
  rcases hg with he | he | he
  · have hh : x p (2*h-1) = true := by
      apply (M.parent6 p (2*h-1) (by have := M.pos; omega)).1 (by have := M.pos; omega)
      convert hB using 1 <;> congr 1 <;> have := M.pos <;> omega
    rw [m0] at hh
    contradiction
  · have hh : x (p-(h : ℤ)) (2*h-1) = true := by
      convert hA using 1 <;> congr 1 <;> omega
    rw [m1] at hh
    contradiction
  · refine ⟨(M.fullRetained h2 (h-1) (by have := M.pos; omega)).1,?_,m2⟩
    convert hA using 1 <;> congr 1 <;> omega

lemma Geometry.backward (M : Geometry h x) (p : ℤ)
    (h0 : Canonical h x p) (h1 : Canonical h x (p-(h : ℤ)))
    (h2 : Canonical h x (p-(2*h : ℕ))) : Canonical h x (p-(3*h : ℕ)) := by
  obtain ⟨a,ha,hA,hB,hact⟩ := M.cover13Active (p-1)
  have cmp (z : ℤ) (hz : Active h x z) :
      p-1-(a : ℤ)=z ∨ p-1-(a : ℤ)+(h : ℤ) ≤ z ∨ z+(h : ℤ) ≤ p-1-(a : ℤ) := by
    rcases lt_trichotomy (p-1-(a : ℤ)) z with hl | he | hr
    · have hs := M.sep hl hact hz
      omega
    · exact Or.inl he
    · have hs := M.sep hr hz hact
      omega
  have c1 := cmp (p-(h : ℤ)) (M.canonicalActive h1)
  have c2 := cmp (p-(2*h : ℕ)) (M.canonicalActive h2)
  have he : p-1-(a : ℤ)=p-(h : ℤ) ∨ p-1-(a : ℤ)=p-(2*h : ℕ) ∨
      p-1-(a : ℤ)=p-(3*h : ℕ) := by push_cast at *; have := M.pos; omega
  rcases he with he | he | he
  · have hh : x (p-(h : ℤ)) (2*h-1) = true := by
      apply (M.parent6 (p-(h : ℤ)) (2*h-1) (by have := M.pos; omega)).1 (by have := M.pos; omega)
      convert hB using 1 <;> congr 1 <;> have := M.pos <;> omega
    rw [h1.2.2] at hh
    contradiction
  · have hh : x (p-(2*h : ℕ)) (2*h-1) = true := by
      convert hA using 1 <;> congr 1 <;> have := M.pos <;> omega
    rw [h2.2.2] at hh
    contradiction
  · have hc : x (p-(3*h : ℕ)) (3*h-1) = true := by
      convert hA using 1 <;> congr 1 <;> have := M.pos <;> omega
    have hc' : x (p-(3*h : ℕ)) (2*h+(h-1)) = true := by
      convert hc using 1 <;> congr 1 <;> have := M.pos <;> omega
    have hz := M.childZ (p-(3*h : ℕ)) (h-1) (by have := M.pos; omega) hc'
    have hlo := (M.parent7 (p-(3*h : ℕ)) (h-1) (by have := M.pos; omega)).1
      (by have := M.pos; omega) (by convert hz using 1 <;> congr 1 <;> omega)
    refine ⟨hlo,hc,?_⟩
    apply Bool.eq_false_iff.mpr
    intro hf
    have h2c : x (p-(2*h : ℕ)) (2*h+(h-1)) = true := by
      convert h2.2.1 using 1 <;> congr 1 <;> have := M.pos <;> omega
    have h2z := M.childZ (p-(2*h : ℕ)) (h-1) (by have := M.pos; omega) h2c
    have heq := M.own7 (p-(3*h : ℕ)) (p-(2*h : ℕ)) (2*h-1) (h-1)
      (by have := M.pos; omega) (by have := M.pos; omega) (by omega) hf
      (by convert (M.ends (p-(3*h : ℕ))).2 using 1 <;> congr 1 <;> have := M.pos <;> omega)
      h2.1 (by convert h2z using 1 <;> congr 1 <;> omega)
    have := M.pos
    omega
end CyclePowerSixteenBlock

namespace CyclePowerSixteenBlock
variable {h : ℕ} {x : ℤ → ℕ → Bool}

lemma Geometry.noHighOverlap (M : Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (p : ℤ) (t s : ℕ) (ht : h ≤ t) (hts : t < s) (hs : s < 2*h)
    (hA : x p t = true) (hC : x p (2*h+t) = true) (hm : x p s = false) : False := by
  have aux : ∀ N : ℕ, ∀ (p : ℤ) (t s : ℕ), 2*h-t=N → h ≤ t → t < s → s < 2*h →
      x p t = true → x p (2*h+t) = true → x p s = false → False := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p t s hN ht hts hs hA hC hm
      obtain ⟨u,v,hu,hv,htv,hAu,hCu,hMu,hAv,hCv,hMv,heq⟩ :=
        cycle_power_eight_block_double_gap_transfer h t s M.pos hts hs x p
          M.lowMono M.parent6 M.exact6 M.exact7 M.cover nov
          (fun p r a b hpr ha hb hpA hpB hrA hrB => M.sep hpr ⟨a,ha,hpA,hpB⟩ ⟨b,hb,hrA,hrB⟩)
          hA hC hm
      by_cases he : v=t
      · have he' := heq he
        omega
      · exact ih (2*h-v) (by omega) (p+(t : ℤ)-(2*h : ℕ)-(v : ℤ)) v (v+s-t)
          rfl (by omega) (by omega) (by omega) hAv hCv hMv
  exact aux (2*h-t) p t s rfl ht hts hs hA hC hm

lemma Geometry.midChildFalse (M : Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    {p : ℤ} (hp : Canonical h x p) : x p (3*h) = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hc' : x p (2*h+h) = true := by convert hc using 1 <;> congr 1 <;> omega
  have ha := nov p h (by have := M.pos; omega) hc'
  by_cases he : h=2*h-1
  · rw [he,hp.2.2] at ha
    contradiction
  · exact M.noHighOverlap nov p h (2*h-1) le_rfl (by have := M.pos; omega)
      (by have := M.pos; omega) ha hc' hp.2.2

lemma Geometry.canonicalTriple (M : Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    {p : ℤ} (hp : Canonical h x p) :
    Canonical h x p ∧ Canonical h x (p-(h : ℤ)) ∧ Canonical h x (p-(2*h : ℕ)) := by
  obtain ⟨u,v,hu,hv,htv,hAu,hCu,hMu,hAv,hCv,hMv,heq⟩ :=
    cycle_power_eight_block_double_gap_transfer h (h-1) (2*h-1) M.pos
      (by have := M.pos; omega) (by have := M.pos; omega) x p
      M.lowMono M.parent6 M.exact6 M.exact7 M.cover nov
      (fun p r a b hpr ha hb hpA hpB hrA hrB => M.sep hpr ⟨a,ha,hpA,hpB⟩ ⟨b,hb,hrA,hrB⟩)
      hp.1 (by convert hp.2.1 using 1 <;> congr 1 <;> have := M.pos <;> omega) hp.2.2
  have hvEq : v=h-1 := by have := M.pos; omega
  have huEq : u=h-1 := by have hh := heq hvEq; have := M.pos; omega
  refine ⟨hp,⟨?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
  · convert hAu using 1 <;> congr 1 <;> have := M.pos <;> omega
  · convert hCu using 1 <;> congr 1 <;> have := M.pos <;> omega
  · convert hMu using 1 <;> congr 1 <;> have := M.pos <;> omega
  · convert hAv using 1 <;> congr 1 <;> have := M.pos <;> omega
  · convert hCv using 1 <;> congr 1 <;> have := M.pos <;> omega
  · convert hMv using 1 <;> congr 1 <;> have := M.pos <;> omega

lemma Geometry.canonicalChain (M : Geometry h x) {p : ℤ}
    (hp : Canonical h x p) (h1 : Canonical h x (p-(h : ℤ))) (h2 : Canonical h x (p-(2*h : ℕ))) :
    ∀ n : ℕ, Canonical h x (p-(n : ℤ)*(h : ℤ)) := by
  have aux (n : ℕ) : Canonical h x (p-(n : ℤ)*(h : ℤ)) ∧
      Canonical h x (p-((n : ℤ)+1)*(h : ℤ)) ∧ Canonical h x (p-((n : ℤ)+2)*(h : ℤ)) := by
    induction n with
    | zero => simpa using And.intro hp (And.intro h1 h2)
    | succ n ih =>
      have hb := M.backward (p-(n : ℤ)*(h : ℤ)) ih.1
        (by convert ih.2.1 using 1 <;> push_cast <;> ring)
        (by convert ih.2.2 using 1 <;> push_cast <;> ring)
      refine ⟨?_,?_,?_⟩
      · convert ih.2.1 using 1 <;> push_cast <;> ring
      · convert ih.2.2 using 1 <;> push_cast <;> ring
      · convert hb using 1 <;> push_cast <;> ring
  exact fun n => (aux n).1
end CyclePowerSixteenBlock

namespace CyclePowerSixteenBlock
variable {h : ℕ} {x : ℤ → ℕ → Bool}

lemma Geometry.forceH0 (M : Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (r : ℤ) (hr : Canonical h x r) (hp : Canonical h x (r+(h : ℤ)))
    (hv : Canonical h x (r+(4*h : ℕ))) : x r (12*h) = true := by
  let v : ℤ := r+(4*h : ℕ)
  let p : ℤ := r+(h : ℤ)
  obtain ⟨a,ha,hA,hB⟩ := M.cover (12*h-1) (by have := M.pos; omega) (by have := M.pos; omega) v
  have ha4 : a ≤ 4*h := by have := M.pos; omega
  let w : ℤ := v-(a : ℤ)
  by_cases ha0 : a=0
  · have hg : x v (12*h-1) = true := by simpa only [ha0,Nat.cast_zero,sub_zero,zero_add] using hB
    have hc : x v (4*h-1) = true := by
      apply (M.parent4 v (4*h-1) (by have := M.pos; omega)).1 (by have := M.pos; omega)
      convert hg using 1 <;> congr 1 <;> have := M.pos <;> omega
    have hc' : x v (2*h+(2*h-1)) = true := by convert hc using 1 <;> congr 1 <;> have := M.pos <;> omega
    have hm := nov v (2*h-1) (by have := M.pos; omega) hc'
    rw [hv.2.2] at hm
    contradiction
  · by_cases ha2 : a ≤ 2*h
    · have hl : x w (a-1) = true := by
        apply (M.parent6 w (a-1) (by omega)).1 (by omega)
        convert hB using 1 <;> congr 1 <;> have := M.pos <;> omega
      have hpZ := M.childZ p (h-1) (by have := M.pos; omega)
        (by convert hp.2.1 using 1 <;> congr 1 <;> have := M.pos <;> omega)
      have he := M.own6 w p (a-1) (3*h-1) (by omega) (by have := M.pos; omega)
        (by dsimp [w,v,p]; have := M.pos; omega) hl
        (by convert hB using 1 <;> congr 1 <;> have := M.pos <;> omega)
        hp.2.1 (by convert hpZ using 1 <;> congr 1 <;> have := M.pos <;> omega)
      dsimp [w,v,p] at he
      have := M.pos
      omega
    · by_cases haEq : a=4*h
      · have hD : x r (4*h) = true := by convert hA using 1 <;> congr 1 <;> (try dsimp [v]) <;> omega
        have hh := (M.parent4 r (4*h) (by have := M.pos; omega)).2 le_rfl hD
        convert hh using 1 <;> congr 1 <;> omega
      · let b := a-2*h
        have hb : b < 2*h := by dsimp [b]; omega
        have hC : x w (2*h+b) = true := by convert hA using 1 <;> congr 1 <;> dsimp [b] <;> omega
        have hw : Active h x w := ⟨b,hb,nov w b hb hC,M.childZ w b hb hC⟩
        have hpAct : Active h x p := M.canonicalActive hp
        have hew : w=p := by
          rcases lt_trichotomy w p with hlt | he | hgt
          · have hs := M.sep hlt hw hpAct
            dsimp [w,v,p] at hs
            have := M.pos
            omega
          · exact he
          · have hs := M.sep hgt hpAct hw
            dsimp [w,v,p] at hs
            have := M.pos
            omega
        dsimp [w,v,p] at hew
        have hc : x p (3*h) = true := by
          convert hA using 1 <;> congr 1 <;> (try dsimp [v,p]) <;> omega
        rw [M.midChildFalse nov hp] at hc
        contradiction

lemma Geometry.cornerFromH0 (M : Geometry h x) (v : ℤ)
    (h0 : Canonical h x v) (h1 : Canonical h x (v-(h : ℤ)))
    (h2 : Canonical h x (v-(2*h : ℕ)))
    (hH : x v (12*h) = true) (hHnext : x (v+(h : ℤ)) (12*h) = true) :
    x (v-(h : ℤ)) h = true ∧ x (v-(h : ℤ)) (14*h) = true := by
  obtain ⟨a,ha,hA,hB,hact⟩ := M.cover13Active v
  have hg := M.grid v (v-(a : ℤ)) hact (M.canonicalActive h0) (M.canonicalActive h1)
    (M.canonicalActive h2) (by omega) (by have := M.pos; omega)
  rcases hg with he | he | he
  · have hh : x v (h+12*h) = true := by convert hB using 1 <;> congr 1 <;> omega
    have hl := (M.parent6 v h (by have := M.pos; omega)).1 (by have := M.pos; omega) hh
    have heq := M.own6 v (v+(h : ℤ)) h 0 (by have := M.pos; omega) (by have := M.pos; omega)
      (by omega) hl hh (M.ends _).1 (by simpa using hHnext)
    have := M.pos
    omega
  · constructor
    · convert hA using 1 <;> congr 1 <;> omega
    · convert hB using 1 <;> congr 1 <;> omega
  · have hc : x (v-(2*h : ℕ)) (2*h+0) = true := by convert hA using 1 <;> congr 1 <;> omega
    have hz := M.childZ (v-(2*h : ℕ)) 0 (by have := M.pos; omega) hc
    have heq := M.own6 (v-(2*h : ℕ)) v (2*h) 0
      (by have := M.pos; omega) (by have := M.pos; omega) (by omega)
      (by simpa using hc) (by convert hz using 1 <;> congr 1 <;> omega)
      (M.ends v).1 (by simpa using hH)
    have := M.pos
    omega

lemma Geometry.chainImpossible (M : Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (p : ℤ) (chain : ∀ n : ℕ, Canonical h x (p-(n : ℤ)*(h : ℤ))) : False := by
  have ch (n : ℕ) : Canonical h x (p-(n : ℤ)*(h : ℤ)) := chain n
  have hf (j : ℕ) (hj : 4 ≤ j) : x (p-(j : ℤ)*(h : ℤ)) (12*h) = true := by
    apply M.forceH0 nov (p-(j : ℤ)*(h : ℤ)) (ch j)
    · convert ch (j-1) using 1 <;> push_cast [Nat.cast_sub (by omega : 1 ≤ j)] <;> ring
    · convert ch (j-4) using 1 <;> push_cast [Nat.cast_sub hj] <;> ring
  have hc5 := M.cornerFromH0 (p-5*(h : ℤ))
    (by simpa using ch 5)
    (by convert ch 6 using 1 <;> push_cast <;> ring)
    (by convert ch 7 using 1 <;> push_cast <;> ring)
    (by simpa using hf 5 (by omega))
    (by convert hf 4 (by omega) using 1 <;> push_cast <;> ring)
  have hc6 := M.cornerFromH0 (p-6*(h : ℤ))
    (by simpa using ch 6)
    (by convert ch 7 using 1 <;> push_cast <;> ring)
    (by convert ch 8 using 1 <;> push_cast <;> ring)
    (by simpa using hf 6 (by omega))
    (by convert hf 5 (by omega) using 1 <;> push_cast <;> ring)
  have hz : x (p-6*(h : ℤ)-(h : ℤ)) (h+14*h) = true := by
    apply M.highMono _ (14*h) (h+14*h) le_rfl (by omega) (by have := M.pos; omega)
    exact hc6.2
  have heq := M.own7 (p-6*(h : ℤ)-(h : ℤ)) (p-5*(h : ℤ)-(h : ℤ)) h 0
    (by have := M.pos; omega) (by have := M.pos; omega) (by ring)
    hc6.1 hz (M.ends _).1 (by simpa using hc5.2)
  have := M.pos
  omega
end CyclePowerSixteenBlock

theorem cycle_power_sixteen_block_no_vertical_overlap
    (h : ℕ) (x : ℤ → ℕ → Bool) (M : CyclePowerSixteenBlock.Geometry h x)
    (nov : ∀ p a, a < 2*h → x p (2*h+a) = true → x p a = true)
    (p : ℤ) (t s : ℕ) (hts : t < s) (hsq : s < 2*h)
    (hA : x p t = true) (hC : x p (2*h+t) = true) (hm : x p s = false) : False := by
  obtain ⟨r,a,b,ha,hb,hbq,hA0,hC0,hm0,hA1,hC1,hm1,hA2,hC2,hm2⟩ :=
    cycle_power_eight_block_overlap_stabilizes h M.pos x M.lowMono M.parent6 M.exact6 M.exact7 M.cover nov
      (fun p r a b hpr ha hb hpA hpB hrA hrB => M.sep hpr ⟨a,ha,hpA,hpB⟩ ⟨b,hb,hrA,hrB⟩)
      p t s hts hsq hA hC hm
  have a0 : CyclePowerSixteenBlock.Active h x r := ⟨a,by omega,hA0,M.childZ r a (by omega) hC0⟩
  have a1 : CyclePowerSixteenBlock.Active h x (r-(h : ℤ)) :=
    ⟨b-h,by omega,hA1,M.childZ _ (b-h) (by omega) hC1⟩
  have a2 : CyclePowerSixteenBlock.Active h x (r-(2*h : ℕ)) :=
    ⟨a,by omega,hA2,M.childZ _ a (by omega) hC2⟩
  have cc := M.maxChildOfThree r a0 a1 a2
    (M.missLast hbq hm0) (M.missLast (by omega) hm1) (M.missLast hbq hm2)
  obtain ⟨c0,c1,c2⟩ := M.canonicalTriple nov cc
  exact M.chainImpossible nov (r-(2*h : ℕ)) (M.canonicalChain c0 c1 c2)
