import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuadConsCons
import AFTD.Kb.Tcs.IsTotallyIsotropic
import AFTD.Kb.Tcs.StandardQuad

/-!
# cylinder_construction_step

Topic: combinatorics   Node: ad8d2ba79bd7

Provenance: helper lemma. step towards cylinder_construction_distance_set

Let $p$ be prime. Given an $m$-dimensional totally isotropic subspace $W \le (\mathbb{Z}/p\mathbb{Z})^d$ and a vector $e \notin W$ orthogonal to $W$ with $Q_d(e) \neq 0$, there exist an $(m+1)$-dimensional totally isotropic subspace $W' \le (\mathbb{Z}/p\mathbb{Z})^{d+2}$ and a vector $e' \notin W'$ orthogonal to $W'$ with $Q_{d+2}(e') \neq 0$.
-/

open Matrix

def cylinder_construction_step_embed (d p : ℕ) :
    (Fin d → ZMod p) →ₗ[ZMod p] (Fin (d+2) → ZMod p) where
  toFun v := Matrix.vecCons 0 (Matrix.vecCons 0 v)
  map_add' v w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.add_apply]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [Pi.add_apply]
      · simp [Pi.add_apply]
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.smul_apply]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [Pi.smul_apply]
      · simp [Pi.smul_apply]

def cylinder_construction_step_wstar {p : ℕ} {d : ℕ} (x y : ZMod p) (e : Fin d → ZMod p) :
    Fin (d+2) → ZMod p := Matrix.vecCons x (Matrix.vecCons y e)

def cylinder_construction_step_estar {p : ℕ} {d : ℕ} (x y : ZMod p) : Fin (d+2) → ZMod p :=
  Matrix.vecCons (-y) (Matrix.vecCons x (0 : Fin d → ZMod p))

lemma cylinder_construction_step_embed_quad {p : ℕ} (d : ℕ) (v : Fin d → ZMod p) :
    standard_quad (d+2) (cylinder_construction_step_embed d p v) = standard_quad d v := by
  show standard_quad (d+2) (Matrix.vecCons 0 (Matrix.vecCons 0 v)) = standard_quad d v
  rw [standard_quad_cons_cons]
  simp

lemma cylinder_construction_step_embed_wstar_dot {p : ℕ} (d : ℕ) (x y : ZMod p)
    (e v : Fin d → ZMod p) :
    dotProduct (cylinder_construction_step_embed d p v) (cylinder_construction_step_wstar x y e)
      = dotProduct v e := by
  simp [cylinder_construction_step_embed, cylinder_construction_step_wstar]

lemma cylinder_construction_step_wstar_quad {p : ℕ} (d : ℕ) (x y : ZMod p) (e : Fin d → ZMod p) :
    standard_quad (d+2) (cylinder_construction_step_wstar x y e) = x^2 + y^2 + standard_quad d e := by
  show standard_quad (d+2) (Matrix.vecCons x (Matrix.vecCons y e)) = x^2+y^2+standard_quad d e
  rw [standard_quad_cons_cons]

lemma cylinder_construction_step_estar_quad {p : ℕ} (d : ℕ) (x y : ZMod p) :
    standard_quad (d+2) (cylinder_construction_step_estar (p:=p) (d:=d) x y) = x^2 + y^2 := by
  show standard_quad (d+2) (Matrix.vecCons (-y) (Matrix.vecCons x (0 : Fin d → ZMod p))) = x^2+y^2
  rw [standard_quad_cons_cons]
  simp [standard_quad]
  ring

lemma cylinder_construction_step_estar_embed_dot {p : ℕ} (d : ℕ) (x y : ZMod p)
    (v : Fin d → ZMod p) :
    dotProduct (cylinder_construction_step_estar (p:=p) (d:=d) x y)
      (cylinder_construction_step_embed d p v) = 0 := by
  simp [cylinder_construction_step_estar, cylinder_construction_step_embed]

lemma cylinder_construction_step_estar_wstar_dot {p : ℕ} (d : ℕ) (x y : ZMod p)
    (e : Fin d → ZMod p) :
    dotProduct (cylinder_construction_step_estar (p:=p) (d:=d) x y)
      (cylinder_construction_step_wstar x y e) = 0 := by
  simp [cylinder_construction_step_estar, cylinder_construction_step_wstar]
  ring

lemma cylinder_construction_step_embed_injective {p : ℕ} (d : ℕ) :
    Function.Injective (cylinder_construction_step_embed d p) := by
  intro v w h
  funext k
  have := congrArg (fun f => f (Fin.succ (Fin.succ k))) h
  simpa [cylinder_construction_step_embed] using this

lemma cylinder_construction_step_quad_add {p : ℕ} (n : ℕ) (a b : Fin n → ZMod p) :
    standard_quad n (a + b) = standard_quad n a + standard_quad n b + 2 * dotProduct a b := by
  simp only [standard_quad, dotProduct, Pi.add_apply]
  rw [show (∑ i, (a i + b i)^2) = ∑ i, (a i^2 + b i^2 + 2*(a i * b i)) from
    Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma cylinder_construction_step_quad_smul {p : ℕ} (n : ℕ) (c : ZMod p) (a : Fin n → ZMod p) :
    standard_quad n (c • a) = c^2 * standard_quad n a := by
  simp only [standard_quad, Pi.smul_apply]
  rw [show (∑ i, (c • a i)^2) = ∑ i, c^2 * (a i)^2 from
    Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul]; ring)]
  rw [Finset.mul_sum]

/-- Inductive step for isotropic subspace construction: given an m-dimensional totally isotropic subspace W in (ZMod p)^d and an orthogonal anisotropic vector e not in W, there exist an (m+1)-dimensional totally isotropic subspace W' in (ZMod p)^(d+2) and an orthogonal anisotropic vector e' not in W'. -/
theorem cylinder_construction_step
    (p : ℕ) [Fact p.Prime] (d m : ℕ)
    (W : Submodule (ZMod p) (Fin d → ZMod p)) (e : Fin d → ZMod p)
    (h_dim : Module.finrank (ZMod p) W = m)
    (h_iso : is_totally_isotropic d W)
    (h_orth : ∀ w ∈ W, dotProduct e w = 0)
    (he : e ∉ W)
    (hκ : standard_quad d e ≠ 0) :
    ∃ (W' : Submodule (ZMod p) (Fin (d + 2) → ZMod p)) (e' : Fin (d + 2) → ZMod p),
      Module.finrank (ZMod p) W' = m + 1 ∧
      is_totally_isotropic (d + 2) W' ∧
      (∀ w ∈ W', dotProduct e' w = 0) ∧
      e' ∉ W' ∧
      standard_quad (d + 2) e' ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := ZMod.sq_add_sq p (-(standard_quad d e))
  let emb := cylinder_construction_step_embed d p
  let wstar := cylinder_construction_step_wstar x y e
  let estar := cylinder_construction_step_estar (p:=p) (d:=d) x y
  let W' : Submodule (ZMod p) (Fin (d+2) → ZMod p) :=
    W.map emb ⊔ Submodule.span (ZMod p) {wstar}
  have hinj : Function.Injective emb := cylinder_construction_step_embed_injective d
  have hwstar_quad0 : standard_quad (d+2) wstar = 0 := by
    have hq : standard_quad (d+2) wstar = x^2 + y^2 + standard_quad d e := by
      simpa only [wstar] using cylinder_construction_step_wstar_quad d x y e
    rw [hq, hxy, neg_add_cancel]
  have hwstar_ne : wstar ≠ 0 := by
    intro h
    have he0 : e = 0 := by
      funext k
      have := congrArg (fun f => f (Fin.succ (Fin.succ k))) h
      simpa [wstar, cylinder_construction_step_wstar] using this
    apply hκ
    rw [he0]
    simp [standard_quad]
  have hwstar_notmem : wstar ∉ W.map emb := by
    intro h
    rw [Submodule.mem_map] at h
    obtain ⟨v, hv, hvq⟩ := h
    have hve : v = e := by
      funext k
      have := congrArg (fun f => f (Fin.succ (Fin.succ k))) hvq
      simpa [emb, cylinder_construction_step_embed, wstar, cylinder_construction_step_wstar] using this
    exact he (hve ▸ hv)
  have hdisj : W.map emb ⊓ Submodule.span (ZMod p) {wstar} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Submodule.mem_span_singleton] at hz2
    obtain ⟨c, hc⟩ := hz2
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc; exact hc.symm
    · exfalso
      apply hwstar_notmem
      have hcw : wstar = c⁻¹ • z := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hcw]
      exact Submodule.smul_mem _ _ hz1
  have hdim_map : Module.finrank (ZMod p) ↥(W.map emb) = m :=
    (Submodule.equivMapOfInjective emb hinj W).finrank_eq.symm.trans h_dim
  have hspan : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {wstar}) = 1 :=
    finrank_span_singleton hwstar_ne
  have hW'_dim : Module.finrank (ZMod p) W' = m + 1 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (W.map emb) (Submodule.span (ZMod p) {wstar})
    rw [hdisj, hdim_map, hspan, finrank_bot, add_zero] at hsup
    simpa only [W'] using hsup
  have hW'_total : is_totally_isotropic (d+2) W' := by
    intro w hw
    dsimp only [W'] at hw
    rw [Submodule.mem_sup] at hw
    obtain ⟨a, ha, b, hb, hwab⟩ := hw
    rw [Submodule.mem_map] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    rw [Submodule.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [← hwab]
    rw [cylinder_construction_step_quad_add, cylinder_construction_step_quad_smul]
    have h1 : standard_quad (d+2) (emb v) = 0 := by
      dsimp only [emb]
      rw [cylinder_construction_step_embed_quad, h_iso v hv]
    have h3 : dotProduct (emb v) (c • wstar) = 0 := by
      rw [dotProduct_smul]
      have hd : dotProduct (emb v) wstar = dotProduct v e := by
        dsimp only [emb, wstar]
        exact cylinder_construction_step_embed_wstar_dot d x y e v
      rw [hd, dotProduct_comm v e, h_orth v hv]
      simp
    rw [h1, hwstar_quad0, h3]
    ring
  have horth : ∀ w ∈ W', dotProduct estar w = 0 := by
    intro w hw
    dsimp only [W'] at hw
    rw [Submodule.mem_sup] at hw
    obtain ⟨a, ha, b, hb, hwab⟩ := hw
    rw [Submodule.mem_map] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    rw [Submodule.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [← hwab, dotProduct_add]
    have h1 : dotProduct estar (emb v) = 0 := by
      dsimp only [estar, emb]
      exact cylinder_construction_step_estar_embed_dot d x y v
    have h2 : dotProduct estar (c • wstar) = 0 := by
      rw [dotProduct_smul]
      have hd : dotProduct estar wstar = 0 := by
        dsimp only [estar, wstar]
        exact cylinder_construction_step_estar_wstar_dot d x y e
      rw [hd]; simp
    rw [h1, h2, add_zero]
  have hQestar : standard_quad (d+2) estar ≠ 0 := by
    have hq : standard_quad (d+2) estar = x^2 + y^2 := by
      simpa only [estar] using cylinder_construction_step_estar_quad (p:=p) (d:=d) x y
    rw [hq, hxy]
    exact neg_ne_zero.mpr hκ
  have hnotmem : estar ∉ W' := by
    intro h
    exact hQestar (hW'_total estar h)
  exact ⟨W', estar, hW'_dim, hW'_total, horth, hnotmem, hQestar⟩
