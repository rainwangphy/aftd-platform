import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalExchangeTakeHead
import AFTD.Kb.Tcs.KruskalExchangeTakeHead'
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachConsIff
import AFTD.Kb.Tcs.KruskalReachLift
import AFTD.Kb.Tcs.KruskalReachMemIff
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalReachOfMem
import AFTD.Kb.Tcs.KruskalReachSymm
import AFTD.Kb.Tcs.G

/-!
# Kruskal.exchange_with_base

Topic: graphs   Node: 39f087fb1cdb

Provenance: helper lemma. TCSlib, `Kruskal.exchange_with_base`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Exchange.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Base-relative exchange of an edge in Kruskal's algorithm. Let $\mathit{base}$ and $S$ be lists of weighted edges on $n$ vertices, and let $e$ be a
weighted edge whose two endpoints are distinct. Suppose the endpoints of $e$ are
connected by a path using the edges of $\mathit{base}$ together with those of $S$, but
are not connected using the edges of $\mathit{base}$ alone. Then there is an edge $f$
occurring in $S$ such that, for every pair of vertices $a$ and $b$ connected by a path
through the edges of $\mathit{base}$ together with $S$, the vertices $a$ and $b$ are
still connected by a path through the edges of $\mathit{base}$ together with the edges
of $S$ after removing one occurrence of $f$ and adjoining $e$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.exchange_with_base {n : ℕ} {base S : List (WEdge n)} {e : WEdge n}
    (hreach : Reach (base ++ S) e.u e.v)
    (hbase : ¬Reach base e.u e.v) (hne : e.u ≠ e.v) :
    ∃ f ∈ S, ∀ a b, Reach (base ++ S) a b →
      Reach (base ++ S.erase f ++ [e]) a b := by
  revert e
  intro e hreach hbase hne
  induction' S with g S ih generalizing base
  · aesop
  · by_cases hcase1 : Reach (base ++ S) e.u e.v
    · specialize ih hcase1 hbase
      obtain ⟨f, hf1, hf2⟩ := ih
      simp_all +decide [List.erase_cons]
      refine Or.inr ⟨f, hf1, fun a b hab => ?_⟩
      split_ifs <;> simp_all +decide
      · apply reach_lift
        rotate_right
        exact base ++ f :: S
        · intro a b hab
          exact reach_mono (by tauto) (by aesop)
        · assumption
      · have h_reach : Reach (base ++ S) a b ∨
            (Reach (base ++ S) a g.u ∧ Reach (base ++ S) g.v b) ∨
            (Reach (base ++ S) a g.v ∧ Reach (base ++ S) g.u b) := by
          have h_iff : Reach (base ++ g :: S) a b ↔ Reach (base ++ S) a b ∨
              (Reach (base ++ S) a g.u ∧ Reach (base ++ S) g.v b) ∨
              (Reach (base ++ S) a g.v ∧ Reach (base ++ S) g.u b) := by
            convert reach_cons_iff using 1
            convert reach_mem_iff _ using 1
            grind
          exact h_iff.mp hab
        rcases h_reach with h | h | h
        · exact reach_mono (hf2 a b h) fun x hx => by aesop
        · have h1 : Reach (base ++ g :: (S.erase f ++ [e])) a g.u :=
            reach_mono (hf2 _ _ h.1) fun x hx => by aesop
          have h2 : Reach (base ++ g :: (S.erase f ++ [e])) g.v b :=
            reach_mono (hf2 _ _ h.2) fun x hx => by aesop
          have hg : Reach (base ++ g :: (S.erase f ++ [e])) g.u g.v :=
            Relation.ReflTransGen.single ⟨g, by aesop⟩
          exact h1.trans (hg.trans h2)
        · have h1 : Reach (base ++ g :: (S.erase f ++ [e])) a g.v :=
            reach_mono (hf2 _ _ h.1) fun x hx => by aesop
          have h2 : Reach (base ++ g :: (S.erase f ++ [e])) g.u b :=
            reach_mono (hf2 _ _ h.2) fun x hx => by aesop
          have hg : Reach (base ++ g :: (S.erase f ++ [e])) g.v g.u :=
            reach_symm (reach_of_mem (by simp +decide :
              g ∈ base ++ g :: (S.erase f ++ [e])))
          exact h1.trans (hg.trans h2)
    · have hswap : Reach (base ++ S) e.u g.u ∧ Reach (base ++ S) g.v e.v ∨
          Reach (base ++ S) e.u g.v ∧ Reach (base ++ S) g.u e.v := by
        have hreach_g : Reach (g :: (base ++ S)) e.u e.v :=
          (reach_mem_iff (by grind)).1 hreach
        cases reach_cons_iff.mp hreach_g <;> aesop
      cases' hswap with hswap hswap
      · have hlift : ∀ a b, Reach (base ++ g :: S) a b → Reach (base ++ S ++ [e]) a b :=
          exchange_take_head hswap.left hswap.right
        aesop
      · have hlift : ∀ a b, Reach (base ++ g :: S) a b → Reach (base ++ S ++ [e]) a b :=
          exchange_take_head' hswap.1 hswap.2
        use g; simp
        simpa only [List.append_assoc] using hlift
