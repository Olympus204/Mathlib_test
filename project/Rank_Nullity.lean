import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.LinearMap
import Mathlib.LinearAlgebra.Submodule
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.LinearIndependent


open Submodule

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V]

variable (f : V →ₗ[K] W)
variable (bKer : Basis ιₖ K (LinearMap.ker f))

noncomputable def bV : Basis (ιₖ ⊕ ιc) K V :=
  (bKer.extend : Basis _ _ _)

noncomputable def bCoker : ιc → V :=
  fun i => (bV (f := f) bKer) (Sum.inr i)

lemma map_bKer_zero (i : ιₖ) :
    f (bV (f := f) bKer (Sum.inl i)) = 0 := by
  classical
  have hmem : bV (f := f) bKer (Sum.inl i) ∈ LinearMap.ker f := by
    simpa using (bKer.extend_inl_mem i)
  simpa using hmem

lemma span_image_bCoker_eq_range :
    Submodule.span K (Set.range (fun i => f (bCoker (f := f) bKer i)))
      = LinearMap.range f :=
by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    intro w hw
    rcases hw with ⟨i, rfl⟩
    exact ⟨bCoker (f := f) bKer i, rfl⟩
  · intro w hw
    rcases hw with ⟨v, rfl⟩
    have hv :
        ∃ coeff : ιₖ ⊕ ιc → K,
          v = ∑ i, coeff i • (bV (f := f) bKer i) :=
      by simpa using (bV (f := f) bKer).exists_coord_eq v
    rcases hv with ⟨coeff, rfl⟩
    simp [LinearMap.map_sum, LinearMap.map_smul, bCoker, bV, map_bKer_zero (f := f) bKer]

lemma linearIndependent_image_bCoker :
    LinearIndependent K (fun i => f (bCoker (f := f) bKer i)) :=
by
  classical
  refine linearIndependent_iff'.2 ?_
  intro coeff hsum
  have h0 :
      f (∑ i, coeff i • bCoker (f := f) bKer i) = 0 := by
    simpa [LinearMap.map_sum, LinearMap.map_smul] using hsum
  have hker :
      (∑ i, coeff i • bCoker (f := f) bKer i) ∈ LinearMap.ker f :=
    h0
  have :
      ∑ i, coeff i • bCoker (f := f) bKer i
        = ∑ j : ιₖ ⊕ ιc,
            (Sum.rec (fun _ => 0) coeff j) •
            (bV (f := f) bKer j) := by
    classical
    have hsplit :
      (∑ i, coeff i • bCoker (f := f) bKer i)
        =
      (∑ j : ιₖ ⊕ ιc, (match j with | Sum.inl _ => 0 | Sum.inr i => coeff i)
          • (bV (f := f) bKer j)) := by
      simp [bCoker, bV]
    exact hsplit
  have hLI := (bV (f := f) bKer).linearIndependent
  have := hLI.sum_eq_zero_iff.mp ?heq
  · intro i; simpa using this (Sum.inr i)
  · sorry

theorem rank_nullity_basis_extension :
    finrank K V =
      finrank K (LinearMap.ker f) +
      finrank K (LinearMap.range f) :=
by
  classical
  have hKer :
      finrank K (LinearMap.ker f) = Fintype.card ιₖ := by
    simpa using (bKer.card_eq_iff.mpr rfl)
  have hImg :
      finrank K (LinearMap.range f) = Fintype.card ιc := by
    let bImg :=
      Basis.mk (linearIndependent_image_bCoker (f := f) bKer)
               (span_image_bCoker_eq_range (f := f) bKer ▸ by simpa)
    simpa using bImg.card_eq_finrank
  have hV : finrank K V = Fintype.card (ιₖ ⊕ ιc) := by
    simpa using (bV (f := f) bKer).card_eq_finrank
  have hCard :
      Fintype.card (ιₖ ⊕ ιc) = Fintype.card ιₖ + Fintype.card ιc :=
    Fintype.card_sum ..
  simp [hV, hKer, hImg, hCard]
