import AFTD.Prelude

/-!
# CoClass

Topic: complexity_basics   Node: 148c95297072

The complement class co(C) of a complexity class C on languages over alphabet α consists of all languages L whose complement is in C.
-/

/-- The complement class coC of a complexity class C consists of languages whose complement is in C. -/
def CoClass {α : Type*} (C : Language α → Prop) : Language α → Prop := fun L => C Lᶜ
