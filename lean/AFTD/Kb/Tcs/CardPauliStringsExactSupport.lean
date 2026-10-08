import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliNZ
import AFTD.Kb.Tcs.PauliNZToBasis
import AFTD.Kb.Tcs.MkWithSupport
import AFTD.Kb.Tcs.PauliStringsExactSupport
import AFTD.Kb.Tcs.Support
import AFTD.Kb.Tcs.SupportMkWithSupport
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.G

/-!
# card_pauliStringsExactSupport

Topic: quantum   Node: d242e0f86951

Provenance: helper lemma. TCSlib, `card_pauliStringsExactSupport`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Number of Pauli strings with a prescribed support. Let $n$ be a natural number and let $S \subseteq \mathrm{Fin}\,n$ be a set of
coordinates. The number of Pauli strings $p$ of length $n$ whose support
$\mathrm{supp}(p)$ equals exactly $S$ is $3^{|S|}$.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
lemma card_pauliStringsExactSupport {n : ℕ} (S : Finset (Fin n)) :
    (pauliStringsExactSupport (n:=n) S).card = 3 ^ S.card := by
  classical
  /-
  Standard proof outline:
  - show the subtype `{p // support p = S}` is in bijection with `S → PauliNZ` via `mkWithSupport`
  - `Fintype.card (S → PauliNZ) = 3^(S.card)`
  - translate to finset-card
  -/
  rw [ show pauliStringsExactSupport S = Finset.image ( fun f : S → PauliNZ => mkWithSupport S f ) ( Finset.univ ) from by
  ext p
  simp [pauliStringsExactSupport]
  constructor <;> intro hp
  · have h_non_id : ∀ i ∈ S, p i ≠ PauliBasis.I := by
      simp +decide [← hp, support]
    use fun i =>
      if p i = PauliBasis.X then PauliNZ.X
      else if p i = PauliBasis.Y then PauliNZ.Y
      else PauliNZ.Z
    funext i
    by_cases hi : i ∈ S <;> simp_all +decide [mkWithSupport]
    · cases hpi : p i <;> aesop
    · unfold support at hp
      subst hp
      simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, not_false_eq_true, implies_true,
        Decidable.not_not]
  · obtain ⟨a, rfl⟩ := hp
    exact support_mkWithSupport S a ];
  · rw [ Finset.card_image_of_injective, Finset.card_univ ] ; aesop;
    intro f g hfg
    have h_eq : ∀ i : S, f i = g i := by
      intro i; replace hfg := congr_fun hfg i; simp_all +decide [ mkWithSupport ] ;
      rcases f_i : f i with ( _ | _ | _ ) <;> rcases g_i : g i with ( _ | _ | _ ) <;> simp_all +decide [ PauliNZ.toBasis ]
    exact funext h_eq;
