import AFTD.Prelude

/-!
# Online.OnlineAlgorithm

Topic: online_algorithms   Node: cfd36113f0d0

Provenance: formalization of a published result. Source: EconCSLib, `Online.OnlineAlgorithm`. Lean proof by Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Algorithm/Online.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A deterministic online algorithm as a state machine. The state `State` summarises the relevant past; `step` consumes the current state and the current input to produce the next state together with an *optional* output — without ever seeing any future input. The input is `Option Input`: `some r` is a genuine request, `none` signals *end of input*, the algorithm's chance to act when the stream is exhausted. A step that emits `some o` halts the run with result `o`; a step that emits `none` defers, recording what it learned into the next state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A deterministic online algorithm as a state machine. The state `State` summarises the relevant past; `step` consumes the current state and the current input to produce the next state together with an *optional* output — without ever seeing any future input. The input is `Option Input`: `some r` is a genuine request, `none` signals *end of input*, the algorithm's chance to act when the stream is exhausted. A step that emits `some o` halts the run with result `o`; a step that emits `none` defers, recording what it learned into the next state. -/
structure Online.OnlineAlgorithm (Input State Output : Type*) where
  /-- Initial state, before any input is processed. -/
  init : State
  /-- One-step transition. Depends only on the current state and the
  current input — by construction, the future is invisible. The input is
  `some r` for a request and `none` for end of input. Emitting `some o`
  halts the run; `none` defers. -/
  step : State → Option Input → State × Option Output
