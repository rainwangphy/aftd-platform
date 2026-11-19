import AFTD.Prelude
import AFTD.Kb.Optimization.SevenArc

/-!
# seven_unsplittable_load

Topic: submodular   Node: c8b01d21973e

Provenance: formalization of a published result. Source: arXiv:2611.23244 Section 4

The load on each arc of the seven-vertex network under demands d_1, d_2, d_3 and unsplittable boolean choices y_1, y_2, y_3, where terminal t_i routes d_i on its arborescence path if y_i is true and on its shortcut path if y_i is false, with arc (s,u) carrying d_3 unconditionally since both paths of t_3 use (s,u).
-/

/-- Load vector on the seven-vertex network induced by an unsplittable routing selection. -/
def seven_unsplittable_load (d1 d2 d3 : ℝ) (y1 y2 y3 : Bool) (arc : SevenArc) : ℝ := match arc with
  | SevenArc.su => (if y1 then d1 else 0) + (if y2 then d2 else 0) + d3
  | SevenArc.uv => (if y1 then d1 else 0) + (if y2 then d2 else 0) + (if y3 then d3 else 0)
  | SevenArc.vw => (if y2 then d2 else 0) + (if y3 then d3 else 0)
  | SevenArc.vt1 => if y1 then d1 else 0
  | SevenArc.wt2 => if y2 then d2 else 0
  | SevenArc.wt3 => if y3 then d3 else 0
  | SevenArc.st1 => if y1 then 0 else d1
  | SevenArc.st2 => if y2 then 0 else d2
  | SevenArc.ut3 => if y3 then 0 else d3
