import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.LinearMap.Defs

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def idLinear : V →ₗ[K] V :=
{ toFun := id,
  map_add' := by simp,
  map_smul' := by simp }

variable (f : V → W)
  (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (a : K) (x : V), f (a • x) = a • f x)

-- Define a linear map by hand:
def myMap :
  V →ₗ[K] W :=
{ toFun := f,
  map_add' := h_add,
  map_smul' := h_smul }

example : V →ₗ[K] W :=
{ toFun := fun x => (2 : K) • (f x)
  map_add' := by
    intro x y
    calc
      (2 : K) • f (x + y) = (2:K) • (f x + f y) := by rw[h_add]
      _= (2:K) • f x + (2:K) • f y := by exact DistribSMul.smul_add 2 (f x) (f y)
  map_smul' := by
    intro a x
    calc
      (2 : K) • f (a • x) = (2 : K) • (a • f x) := by rw[h_smul]
     _= a • (2:K) • f x := by exact smul_comm 2 a (f x)
}
