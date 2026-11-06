import Calderon.SupportedFiniteClmWeightedL2Convergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

theorem tendsto_integral_firstOrder_of_value_and_derivative_tendsto
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (S : Set R3) (hS : IsCompact S)
    (U : ℕ → R3 → V) (u : R3 → V)
    (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hu : ContDiff ℝ ∞ u)
    (hSuppU : ∀ n, tsupport (U n) ⊆ S) (hSuppu : tsupport u ⊆ S)
    (A : Fin 3 → R3 → V →L[ℝ] W) (B : R3 → V →L[ℝ] W)
    (hA : ∀ k, ∀ y ∈ S, ContinuousAt (A k) y) (hB : ∀ y ∈ S, ContinuousAt B y)
    (hValue : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖U n y - u y‖^2) atTop (𝓝 0))
    (hDerivative : ∀ X : R3, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖fderiv ℝ (U n) y X - fderiv ℝ u y X‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖((∑ k : Fin 3, A k y (fderiv ℝ (U n) y (EuclideanSpace.single k 1))) + B y (U n y)) -
        ((∑ k : Fin 3, A k y (fderiv ℝ u y (EuclideanSpace.single k 1))) + B y (u y))‖^2)
      atTop (𝓝 0) := by
  classical
  let E : Option (Fin 3) → ℕ → R3 → V := fun k =>
    match k with
    | none => fun n y => U n y - u y
    | some j => fun n y => fderiv ℝ (U n) y (EuclideanSpace.single j 1) -
        fderiv ℝ u y (EuclideanSpace.single j 1)
  let C : Option (Fin 3) → R3 → V →L[ℝ] W := fun k =>
    match k with
    | none => B
    | some j => A j
  have hE : ∀ k n, Continuous (E k n) := by
    intro k n
    cases k with
    | none => exact (hU n).continuous.sub hu.continuous
    | some j =>
      exact (((hU n).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.sub
        ((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hSupp : ∀ k n, tsupport (E k n) ⊆ S := by
    intro k n
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hnOut : y ∉ tsupport (U n) := fun h => hOutside (hSuppU n h)
    have hOut : y ∉ tsupport u := fun h => hOutside (hSuppu h)
    cases k with
    | none => exact hy (by simp only [E,image_eq_zero_of_notMem_tsupport hnOut,
        image_eq_zero_of_notMem_tsupport hOut,sub_self])
    | some j => exact hy (by simp only [E,fderiv_of_notMem_tsupport ℝ hnOut,
        fderiv_of_notMem_tsupport ℝ hOut,ContinuousLinearMap.zero_apply,sub_self])
  have hC : ∀ k, ∀ y ∈ S, ContinuousAt (C k) y := by
    intro k
    cases k with
    | none => exact hB
    | some j => exact hA j
  have hLimit : ∀ k, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖E k n y‖^2) atTop (𝓝 0) := by
    intro k
    cases k with
    | none => exact hValue
    | some j => exact hDerivative (EuclideanSpace.single j 1)
  have h := tendsto_integral_supported_finite_clm_of_integral_tendsto
    g hg L lam S hS E hE hSupp C hC hLimit
  have hEq (n : ℕ) (y : R3) : (∑ k, C k y (E k n y)) =
      ((∑ k : Fin 3, A k y (fderiv ℝ (U n) y (EuclideanSpace.single k 1))) + B y (U n y)) -
        ((∑ k : Fin 3, A k y (fderiv ℝ u y (EuclideanSpace.single k 1))) + B y (u y)) := by
    rw [Fintype.sum_option]
    simp only [E,C,map_sub,Finset.sum_sub_distrib]
    abel
  simpa only [hEq] using h

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
