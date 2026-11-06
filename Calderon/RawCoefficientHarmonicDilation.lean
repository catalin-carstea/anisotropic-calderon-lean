import Calderon.PositiveCoefficientInnerPointwiseEquation
import Calderon.InwardSmoothBallRealization

/-! EXPANSION.json precedes the raw coefficient local homothety calculation.
The conformal coefficient stays literal; no physical harmonicity premise is introduced. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Gradient InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator

theorem coordinateFluxDivergence_rawGradient_congr_of_eventuallyEq
    (A : MatrixField) (u v : R3 → ℝ) (x : R3) (h : u =ᶠ[𝓝 x] v) :
    coordinateFluxDivergence (fun y => matrixOperatorMap (A y) (gradient u y : R3)) x =
      coordinateFluxDivergence (fun y => matrixOperatorMap (A y) (gradient v y : R3)) x := by
  have hFlux : (fun y => matrixOperatorMap (A y) (gradient u y : R3)) =ᶠ[𝓝 x]
      (fun y => matrixOperatorMap (A y) (gradient v y : R3)) :=
    h.gradient.mono (fun y hy => congrArg (matrixOperatorMap (A y)) hy)
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => (matrixOperatorMap (A y) (gradient u y : R3)) i) =ᶠ[𝓝 x]
      (fun y => (matrixOperatorMap (A y) (gradient v y : R3)) i) :=
    hFlux.mono (fun y hy => congrArg (fun V : R3 => V i) hy)
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq

theorem coordinateFluxDivergence_rawGradient_dilation
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (q : ℝ) (u : SmoothData) (x : R3) :
    coordinateFluxDivergence
      (fun y => matrixOperatorMap (A (q • y)) (gradient (fun z : R3 => u.1 (q • z)) y : R3)) x =
      q^2 * coordinateFluxDivergence
        (fun y => matrixOperatorMap (A y) (gradient u.1 y : R3)) (q • x) := by
  classical
  let Z : R3 → R3 := fun y => matrixOperatorMap (A y) (gradient u.1 y : R3)
  have hGradientCoordinate (j : Fin 3) : ContDiff ℝ ∞ (fun y => (gradient u.1 y : R3) j) := by
    have hDirectional : ContDiff ℝ ∞ (fun y => fderiv ℝ u.1 y (MetricVolume.coordinateVector j)) :=
      (u.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    apply contDiffOn_univ.mp
    exact hDirectional.contDiffOn.congr (fun y _ => by
      simpa only [gradient] using MetricVolume.riesz_coordinate (fderiv ℝ u.1 y) j)
  have hRow (i : Fin 3) : ContDiff ℝ ∞ (fun y => Z y i) := by
    have hSum : ContDiff ℝ ∞ (fun y => ∑ j : Fin 3, A y i j * (gradient u.1 y : R3) j) :=
      ContDiff.sum (fun j _ => (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul (hGradientCoordinate j))
    apply contDiffOn_univ.mp
    exact hSum.contDiffOn.congr (fun y _ => by
      dsimp only [Z]
      exact MetricVolume.matrixOperator_coordinate (A y) (gradient u.1 y : R3) i)
  have hFlux :
      (fun y => matrixOperatorMap (A (q • y)) (gradient (fun z : R3 => u.1 (q • z)) y : R3)) =
      (fun y => q • Z (q • y)) := by
    funext y
    rw [DirichletFamily.gradient_comp_const_smul u.1 q y
      ((u.2.differentiable (by simp)) (q • y)),map_smul]
  have hCoordinate (i : Fin 3) :
      fderiv ℝ (fun y => (q • Z (q • y)) i) x (NormalCoordinatesFrame.coordinateVector i) =
      q^2 * fderiv ℝ (fun y => Z y i) (q • x) (NormalCoordinatesFrame.coordinateVector i) := by
    have hComp : HasFDerivAt (fun y : R3 => q * Z (q • y) i)
        (q • ((fderiv ℝ (fun y => Z y i) (q • x)).comp
          (q • ContinuousLinearMap.id ℝ R3))) x :=
      (((hRow i).differentiable (by simp) (q • x)).hasFDerivAt.comp x
        (q • ContinuousLinearMap.id ℝ R3).hasFDerivAt).const_mul q
    have hComp' : HasFDerivAt (fun y : R3 => (q • Z (q • y)) i)
        (q • ((fderiv ℝ (fun y => Z y i) (q • x)).comp
          (q • ContinuousLinearMap.id ℝ R3))) x := by
      simpa only [PiLp.smul_apply,smul_eq_mul] using hComp
    rw [hComp'.fderiv]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
    ring
  rw [hFlux]
  change (∑ i : Fin 3, fderiv ℝ (fun y => (q • Z (q • y)) i) x
      (NormalCoordinatesFrame.coordinateVector i)) =
    q^2 * (∑ i : Fin 3, fderiv ℝ (fun y => Z y i) (q • x)
      (NormalCoordinatesFrame.coordinateVector i))
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hCoordinate i)

theorem coordinateFluxDivergence_rawGradient_dilation_of_contDiffOn
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (q : ℝ)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (x : R3) (hx : q • x ∈ S) :
    coordinateFluxDivergence
      (fun y => matrixOperatorMap (A (q • y)) (gradient (fun z : R3 => u (q • z)) y : R3)) x =
      q^2 * coordinateFluxDivergence
        (fun y => matrixOperatorMap (A y) (gradient u y : R3)) (q • x) := by
  have hCover : ({q • x} : Set R3) ⊆ S := by
    intro y hy
    rw [mem_singleton_iff] at hy
    simpa only [hy] using hx
  obtain ⟨v,_,hNear⟩ := DirichletFamily.exists_smoothData_eq_near_compact
    ({q • x} : Set R3) S isCompact_singleton hS hCover u hu
  have hvu : v.1 =ᶠ[𝓝 (q • x)] u := hNear (q • x) (mem_singleton (q • x))
  have hvuq : (fun y : R3 => v.1 (q • y)) =ᶠ[𝓝 x] (fun y : R3 => u (q • y)) :=
    (q • ContinuousLinearMap.id ℝ R3).continuous.continuousAt.tendsto.eventually hvu
  calc
    _ = coordinateFluxDivergence
        (fun y => matrixOperatorMap (A (q • y)) (gradient (fun z : R3 => v.1 (q • z)) y : R3)) x :=
      (coordinateFluxDivergence_rawGradient_congr_of_eventuallyEq
        (fun y => A (q • y)) (fun z : R3 => v.1 (q • z)) (fun z : R3 => u (q • z)) x hvuq).symm
    _ = q^2 * coordinateFluxDivergence
        (fun y => matrixOperatorMap (A y) (gradient v.1 y : R3)) (q • x) :=
      coordinateFluxDivergence_rawGradient_dilation A hA q v x
    _ = _ := congrArg (fun r : ℝ => q^2 * r)
      (coordinateFluxDivergence_rawGradient_congr_of_eventuallyEq A v.1 u (q • x) hvu)

end OAI.AnisotropicCalderon.ConnectionError
#print axioms OAI.AnisotropicCalderon.ConnectionError.coordinateFluxDivergence_rawGradient_congr_of_eventuallyEq
#print axioms OAI.AnisotropicCalderon.ConnectionError.coordinateFluxDivergence_rawGradient_dilation
#print axioms OAI.AnisotropicCalderon.ConnectionError.coordinateFluxDivergence_rawGradient_dilation_of_contDiffOn
