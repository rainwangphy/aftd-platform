import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAliceComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAlice
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolCompleteTreeAliceRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.encode_alice

Topic: communication   Node: b933dd068aec

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.encode_alice`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Binary encoding of a finite-alphabet message from Alice. Let $X$, $Y$, and $\alpha$ be types, let $\beta$ be a finite nonempty type, let $f : X
\to \beta$ be a function, and let $Q : \beta \to \mathrm{Protocol}\,X\,Y\,\alpha$ assign
to each value $b \in \beta$ a deterministic two-party communication protocol. Then there
exists a deterministic protocol $R$ over the same input types such that, on every pair
of inputs $x : X$ and $y : Y$, running $R$ yields the same output as running the
protocol $Q(f(x))$, and the communication complexity of $R$ equals
\[
\lceil \log_2 \abs{\beta} \rceil \;+\; \max_{b \in \beta}
\operatorname{complexity}(Q(b)),
\]
where $\abs{\beta}$ denotes the cardinality of $\beta$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Given a function `f : X → β` and binary protocols `Q b` for each `b : β`, there is a single binary protocol `R` that behaves like `Q (f x)` on every input and whose complexity is exactly `⌈log₂ |β|⌉` plus the maximum complexity of the `Q b`: Alice sends `f x` encoded in `⌈log₂ |β|⌉` bits via a complete binary tree, then the parties continue with `Q (f x)`. **Proof sketch.** Let `d = ⌈log₂ |β|⌉`. (1) Encode `β` injectively into `Fin d → Bool` by composing `Fintype.equivFin` with the binary digits: injectivity holds because `|β| ≤ 2 ^ d`, so bits at positions `≥ d` are all zero. (2) Let Alice's `i`-th query on input `x` be the `i`-th bit of `encode (f x)`. (3) Define the continuation at a bit vector: if the vector encodes some (necessarily unique) `b`, continue with `Q b`, otherwise with `Q b₀` for a fixed `b₀`. Take `R` to be the complete Alice tree of depth `d` with these queries and continuations. (4) Outcome: by `completeTreeAlice_run` the tree reaches the continuation at `encode (f x)`, which is `Q (f x)` by injectivity. (5) Complexity: by `completeTreeAlice_complexity` it is `d + sup` over bit vectors of the continuation's complexity, and that supremum equals `sup_b (Q b).complexity` because every continuation is some `Q b` and every `Q b` occurs (at `encode b`). -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.encode_alice {X Y α β : Type*} [Fintype β] [Nonempty β] (f : X → β)
    (Q : β → Deterministic.Protocol X Y α) :
    ∃ R : Deterministic.Protocol X Y α,
      (∀ x y, R.run x y = (Q (f x)).run x y) ∧
      R.complexity = Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun b => (Q b).complexity) := by
  have hcard : 0 < Fintype.card β := Fintype.card_pos
  let b₀ : β := (Fintype.equivFin β).symm ⟨0, hcard⟩
  let d := Nat.clog 2 (Fintype.card β)
  -- Step 1: binary encoding `β → (Fin d → Bool)` via `Fintype.equivFin` then `testBit`,
  -- injective because `|β| ≤ 2 ^ d`
  let encode : β → (Fin d → Bool) := fun b =>
    fun i => (Fintype.equivFin β b).val.testBit i.val
  have hencode_inj : Function.Injective encode := by
    intro a b hab
    apply (Fintype.equivFin β).injective; apply Fin.ext
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < d
    · exact congr_fun hab ⟨i, hi⟩
    · have hd : Fintype.card β ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) _
      have hle := hd.trans
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
      rw [Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β a).isLt hle),
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β b).isLt hle)]
  -- Upgrade ∃ to ∃! using injectivity, for use with Fintype.choose
  have hencode_unique : ∀ bits, (∃ b, encode b = bits) → ∃! b, encode b = bits := by
    intro bits ⟨b, hb⟩; exact ⟨b, hb, fun c hc => hencode_inj (hc.trans hb.symm)⟩
  -- Step 2: Alice's queries are the bits of `encode (f x)`
  let query : Fin d → X → Bool := fun i x => encode (f x) i
  -- Step 3: the continuation at each bit pattern, decoding via `Fintype.choose` when possible
  let leafQ : (Fin d → Bool) → Deterministic.Protocol X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits) (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · -- Step 4: outcome — the tree reaches the continuation at `encode (f x)`, i.e. `Q (f x)`
    intro x y
    rw [completeTreeAlice_run]
    have hquery : (fun i => query i x) = encode (f x) := rfl
    rw [hquery]
    have hexists : ∃ b, encode b = encode (f x) := ⟨f x, rfl⟩
    simp only [leafQ, hexists, dite_true]
    -- Fintype.choose picks the unique b with encode b = encode (f x); by injectivity it's f x
    have hch := Fintype.choose_spec (fun b => encode b = encode (f x)) (hencode_unique _ hexists)
    rw [hencode_inj hch]
  · -- Step 5: complexity — the supremum over bit patterns equals the supremum over `β`
    rw [completeTreeAlice_complexity]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le; intro bits _
      by_cases h : ∃ b, encode b = bits
      · simp only [leafQ, h, dite_true]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
      · simp only [leafQ, h, dite_false]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
    · apply Finset.sup_le; intro b _
      have hleafQ : leafQ (encode b) = Q b := by
        have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
        simp only [leafQ, hexb, dite_true]
        congr 1
        have hch := Fintype.choose_spec (fun b' => encode b' = encode b) (hencode_unique _ hexb)
        exact hencode_inj hch
      calc (Q b).complexity
          = (leafQ (encode b)).complexity := by rw [hleafQ]
        _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
            Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)
