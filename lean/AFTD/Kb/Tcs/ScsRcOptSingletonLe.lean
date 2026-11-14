import AFTD.Prelude
import AFTD.Kb.Tcs.ScsRcOpt
import AFTD.Kb.Tcs.RevComp

/-!
# scs_rc_opt_singleton_le

Topic: approximation   Node: f6ae4446b748

Provenance: helper lemma. Sanity check of scs_rc_opt (arXiv:2611.16573)

The SCS-RC optimum of a single string is at most its length.
-/

theorem scs_rc_opt_singleton_le {Γ : Type*} (cm : Γ → Γ) (s : List Γ) :
    scs_rc_opt cm {s} ≤ s.length :=
  Nat.sInf_le ⟨s, rfl, by simp⟩
