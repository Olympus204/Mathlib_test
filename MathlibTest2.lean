import Mathlib.Algebra.Group.Defs

example [pG : Group G] : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g
