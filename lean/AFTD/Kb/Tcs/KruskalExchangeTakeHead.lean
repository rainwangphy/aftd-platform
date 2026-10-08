import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachLift
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalReachOfMem
import AFTD.Kb.Tcs.KruskalReachSymm
import AFTD.Kb.Tcs.G

/-!
# Kruskal.exchange_take_head

Topic: graphs   Node: 0ce2d0693998

Provenance: helper lemma. TCSlib, `Kruskal.exchange_take_head`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Exchange.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Head-edge exchange preserves reachability. Let $\mathit{base}$ and $\mathit{rest}$ be lists of weighted edges on $n$ vertices, and
let $g$ and $e$ be two further weighted edges, with respective endpoints $u_g, v_g$ and
$u_e, v_e$. Suppose that, using only the edges in the concatenation $\mathit{base}
\mathbin{+\!\!+} \mathit{rest}$, the vertex $u_e$ is connected to $u_g$ and the vertex
$v_g$ is connected to $v_e$. Then for every pair of vertices $a, b$ that are connected
using the edges of $\mathit{base} \mathbin{+\!\!+} (g :: \mathit{rest})$, the vertices
$a$ and $b$ are also connected using the edges of $\mathit{base} \mathbin{+\!\!+}
\mathit{rest} \mathbin{+\!\!+} [e]$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.exchange_take_head {n : ℕ} {base rest : List (WEdge n)} {g e : WEdge n}
    (h1 : Reach (base ++ rest) e.u g.u) (h2 : Reach (base ++ rest) g.v e.v) :
    ∀ a b, Reach (base ++ g :: rest) a b → Reach (base ++ rest ++ [e]) a b := by
  have mono : ∀ {x y}, Reach (base ++ rest) x y → Reach (base ++ rest ++ [e]) x y :=
    fun h => reach_mono h fun _ hx => List.mem_append_left _ hx
  have he_adj : Reach (base ++ rest ++ [e]) e.u e.v :=
    reach_of_mem (by simp)
  intro a b h
  apply reach_lift (edges := base ++ g :: rest) _ h
  intro c d ⟨f, hmem, hadj⟩
  by_cases hfg : f = g
  · subst hfg
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ((reach_symm (mono h1)).trans he_adj).trans (reach_symm (mono h2))
    · exact ((mono h2).trans (reach_symm he_adj)).trans (mono h1)
  · refine Relation.ReflTransGen.single ⟨f, ?_, hadj⟩
    simp only [List.mem_append, List.mem_cons] at hmem ⊢
    tauto
