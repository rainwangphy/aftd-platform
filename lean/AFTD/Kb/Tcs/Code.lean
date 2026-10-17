import AFTD.Prelude

/-!
# Code

Topic: information   Node: f4657fc8a8ae

Provenance: formalization of a published result. Source: QuantumInfo, `Code`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Capacity.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Here we define a *Code* by an encdoder and a decoder. The encoder is a function that takes strings (`List`s) of any length over an alphabet `A`, and returns strings over `I`; the decoder takes `O` and gives back strings over `A`. The idea is that a channel would map from strings of `I` to `O`. Important special cases are where `I=O` (the channel doesn't change the symbol set), and `FixedLengthCode` where the output lengths only depend on input lengths.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A I O : Type*) in
/-- Here we define a *Code* by an encdoder and a decoder. The encoder is a function that takes strings (`List`s) of any length over an alphabet `A`, and returns strings over `I`; the decoder takes `O` and gives back strings over `A`. The idea is that a channel would map from strings of `I` to `O`. Important special cases are where `I=O` (the channel doesn't change the symbol set), and `FixedLengthCode` where the output lengths only depend on input lengths. -/
structure Code where
  encoder : List A → List I
  decoder : List O → List A
