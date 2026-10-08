import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalReachOfMem
import AFTD.Kb.Tcs.KruskalReachSymm
import AFTD.Kb.Tcs.G

/-!
# Kruskal.reach_cons_iff

Topic: graphs   Node: 7b428798e7ee

Provenance: helper lemma. TCSlib, `Kruskal.reach_cons_iff`. Lean proof by [Your Name], [Partner's Name (if applicable)], from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Reach.lean (Copyright (c) 2026 [Your Name] and [Partner's Name (if applicable)]. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Head–tail decomposition of reachability. Let $g$ be a weighted edge on $n$ vertices with endpoints $p$ and $q$, let
$\mathit{rest}$ be a list of weighted edges on the same $n$ vertices, and let $a$ and
$b$ be vertices; say two vertices are \emph{$\mathit{rest}$-connected} when they are
joined by a path using only the edges in $\mathit{rest}$. Then $a$ and $b$ are joined by
a path through the edges of the list obtained by prepending $g$ to $\mathit{rest}$ if
and only if at least one of the following holds: $a$ and $b$ are
$\mathit{rest}$-connected; or $a$ is $\mathit{rest}$-connected to $p$ while $q$ is
$\mathit{rest}$-connected to $b$; or $a$ is $\mathit{rest}$-connected to $q$ while $p$
is $\mathit{rest}$-connected to $b$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reach_cons_iff {n : ℕ} {g : WEdge n} {rest : List (WEdge n)} {a b : Fin n} :
    Reach (g :: rest) a b ↔
      Reach rest a b ∨
      (Reach rest a g.u ∧ Reach rest g.v b) ∨
      (Reach rest a g.v ∧ Reach rest g.u b) := by
  have mono : ∀ {x y}, Reach rest x y → Reach (g :: rest) x y :=
    fun h => reach_mono h fun _ => List.mem_cons_of_mem _
  have gadj : Reach (g :: rest) g.u g.v :=
    Relation.ReflTransGen.single ⟨g, List.mem_cons_self .., Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨fun h => ?_, ?_⟩
  · induction' h with c d hcd ih
    · exact Or.inl .refl
    · rcases ih with ⟨e, he, he'⟩
      rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all +decide [Reach]
      · rcases he with rfl | he
        · aesop
        · rename_i h
          rcases h with h | h | h
          · exact Or.inl <| h.tail ⟨e, he, by tauto⟩
          · exact Or.inr <| Or.inl ⟨h.1, h.2.tail ⟨e, he, by tauto⟩⟩
          · exact Or.inr <| Or.inr ⟨h.1, h.2.tail ⟨e, he, by tauto⟩⟩
      · -- Backward edge: c = e.v, b = e.u. Use the IH for e.v, then reverse via e.
        rename_i h
        rcases he with rfl | he
        · -- e = g: IH is about g.v, goal is about g.u
          rcases h with h | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inr (Or.inr ⟨h, .refl⟩)
          · exact Or.inl h1
          · exact Or.inr (Or.inr ⟨h1, .refl⟩)
        · -- e ∈ rest: Reach rest e.v e.u by symmetry, then chain
          have hrev := reach_symm (reach_of_mem he)
          rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (h.trans hrev)
          · exact Or.inr (Or.inl ⟨h1, h2.trans hrev⟩)
          · exact Or.inr (Or.inr ⟨h1, h2.trans hrev⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mono h
    · exact (mono h1).trans (gadj.trans (mono h2))
    · exact (mono h1).trans ((reach_symm gadj).trans (mono h2))
