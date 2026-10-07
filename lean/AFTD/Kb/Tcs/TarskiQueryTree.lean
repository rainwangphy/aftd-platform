import AFTD.Prelude

/-!
# TarskiQueryTree

Topic: algorithms   Node: e73c4a03b5ea

Provenance: formalization of a published result. Source: arXiv:2610.07055 (Tarski fixed points in quasi-FPT queries), Sec. 1 (the black-box query model; deterministic algorithms as decision trees)

A deterministic adaptive query algorithm for an unknown map f : [n]^k → [n]^k, as a decision tree: a leaf outputs a point; an internal node queries f at a point x and continues according to the value f(x).
-/

/-- A deterministic adaptive query algorithm for a black-box map `[n]^k → [n]^k`, as a decision tree: a leaf outputs a point; an internal node queries the map at a point and branches on the returned value. -/
inductive TarskiQueryTree (n k : ℕ) | output : (Fin k → Fin n) → TarskiQueryTree n k
  | query : (Fin k → Fin n) → ((Fin k → Fin n) → TarskiQueryTree n k) → TarskiQueryTree n k
