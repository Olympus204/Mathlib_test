import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.LinearMap.Defs

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def idLinear : V →ₗ[K] V :=
{ toFun := id,
  map_add' := by simp,
  map_smul' := by simp }

open Function

noncomputable section

-- Inverse of a linear isomorphism is linear.
def inverse_map (f : V →ₗ[K] V) (h : Bijective f) : V →ₗ[K] V :=
{
  toFun := invFun f.toFun,
  map_add' := by
    intro w₁ w₂
    let p := f.toFun
    let q := invFun f.toFun
    let v₁ := q w₁
    let v₂ := q w₂
    have h₁ : v₁ + v₂ = q (w₁ + w₂) := by
      have h₃ : p (v₁ + v₂) = p (v₁) + p (v₂) := by
        exact f.map_add' v₁ v₂
      have w₁' : p (v₁) = w₁ := by
        exact rightInverse_invFun h.surjective w₁
      have w₂' : p (v₂) = w₂ := by
        exact rightInverse_invFun h.surjective w₂
      rw [w₁', w₂'] at h₃
      calc
        v₁ + v₂ = q (p (v₁ + v₂)) := (leftInverse_invFun h.injective (v₁ + v₂)).symm
        _ = q (w₁ + w₂) := by rw[h₃]
    rw[h₁]


    ,
  map_smul' := by
    intro a w
    let p := f.toFun
    let q := invFun f.toFun
    let v := q w
    have h₁ : a • v = q (a • w) := by
      have h₂ : p (a • v) = a • p (v) := by
        exact f.map_smul' a v
      have w' : p (v) = w := by
        exact rightInverse_invFun h.surjective w
      rw[w'] at h₂
      calc
        a • v = q (p (a • v)) := (leftInverse_invFun h.injective (a • v)).symm
        _ = q (a • w) := by rw[h₂]
    change invFun f.toFun (a • w) = a • invFun f.toFun w
    rw[h₁]
}
