import Calderon.PositiveConformalMetric
import Calderon.ConformalReferenceOperators
import Calderon.MetricFrameOperator
import Mathlib.Analysis.Calculus.Gradient.Basic
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator NormalCoordinatesFrame

def coordinateFluxDivergence (Z : R3 → R3) (x : R3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => Z y i) x (coordinateVector i)

def metricDivergenceFlux (g : MatrixField) (u : R3 → ℝ) (x : R3) : R3 :=
  matrixOperatorMap (principalCoefficient g x) (gradient u x)

theorem covector_coordinateFlux (t : R3 → ℝ) (Z : R3 → R3) (x : R3) :
    (∑ i : Fin 3, fderiv ℝ t x (coordinateVector i) * Z x i) = fderiv ℝ t x (Z x) := by
  have hx : (∑ i : Fin 3, Z x i • coordinateVector i) = Z x := by
    ext j
    simp [coordinateVector,Pi.single_apply]
  calc
    _ = fderiv ℝ t x (∑ i : Fin 3, Z x i • coordinateVector i) := by
      simp only [map_sum,map_smul,smul_eq_mul,mul_comm]
    _ = _ := congrArg (fderiv ℝ t x) hx

theorem coordinateFluxDivergence_exp_depth
    (t : R3 → ℝ) (Z : R3 → R3) (L : ℝ) (x : R3)
    (ht : DifferentiableAt ℝ t x) (hZ : DifferentiableAt ℝ Z x) :
    coordinateFluxDivergence (fun y => Real.exp (-L*t y) • Z y) x =
      Real.exp (-L*t x) * (coordinateFluxDivergence Z x - L*fderiv ℝ t x (Z x)) := by
  have hE : HasFDerivAt (fun y : R3 => Real.exp (-L*t y))
      (Real.exp (-L*t x) • (-L • fderiv ℝ t x)) x :=
    (ht.hasFDerivAt.const_mul (-L)).exp
  have hi (i : Fin 3) : DifferentiableAt ℝ (fun y => Z y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hZ
  have hterm (i : Fin 3) :
      fderiv ℝ (fun y => (Real.exp (-L*t y) • Z y) i) x (coordinateVector i) =
        Real.exp (-L*t x)*fderiv ℝ (fun y => Z y i) x (coordinateVector i) -
          Real.exp (-L*t x)*L*(fderiv ℝ t x (coordinateVector i)*Z x i) := by
    change fderiv ℝ (fun y => Real.exp (-L*t y)*Z y i) x (coordinateVector i) = _
    rw [fderiv_fun_mul hE.differentiableAt (hi i),hE.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  unfold coordinateFluxDivergence
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,covector_coordinateFlux]
  ring

theorem coordinateFluxDivergence_exp_depth_drift
    (t : R3 → ℝ) (Z : R3 → R3) (L : ℝ) (x : R3)
    (ht : DifferentiableAt ℝ t x) (hZ : DifferentiableAt ℝ Z x) :
    coordinateFluxDivergence (fun y => Real.exp (-L*t y) • Z y) x +
      L*fderiv ℝ t x (Real.exp (-L*t x) • Z x) =
        Real.exp (-L*t x)*coordinateFluxDivergence Z x := by
  rw [coordinateFluxDivergence_exp_depth t Z L x ht hZ,map_smul]
  simp only [smul_eq_mul]
  ring

theorem coordinateFluxDivergence_exp_depth_zero_iff
    (t : R3 → ℝ) (Z : R3 → R3) (L : ℝ) (x : R3)
    (ht : DifferentiableAt ℝ t x) (hZ : DifferentiableAt ℝ Z x) :
    coordinateFluxDivergence Z x = 0 ↔
      coordinateFluxDivergence (fun y => Real.exp (-L*t y) • Z y) x +
        L*fderiv ℝ t x (Real.exp (-L*t x) • Z x) = 0 := by
  rw [coordinateFluxDivergence_exp_depth_drift t Z L x ht hZ]
  simp only [mul_eq_zero,Real.exp_ne_zero,false_or]

theorem metricDivergenceFlux_conformal (g : MatrixField) (hp : ∀ x, (g x).PosDef)
    (t u : R3 → ℝ) (L : ℝ) :
    metricDivergenceFlux (conformalMatrix g (fun x => -L*t x)) u =
      fun x => Real.exp (-L*t x) • metricDivergenceFlux g u x := by
  funext x
  simp only [metricDivergenceFlux,principalCoefficient_conformalMatrix g _ hp,
    map_smul,ContinuousLinearMap.smul_apply]

theorem contDiff_actual_scalarGradient (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gradient u) :=
  (InnerProductSpace.toDual ℝ R3).symm.contDiff.comp (hu.fderiv_right (by simp))

theorem contDiff_metricDivergenceFlux (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (metricDivergenceFlux g u) :=
  (matrixOperatorMap.contDiff.comp (contDiff_principalCoefficient_of_smooth_posDef g hs hp)).clm_apply
    (contDiff_actual_scalarGradient u hu)

theorem metricDivergenceFlux_conformal_zero_iff (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (t u : R3 → ℝ) (ht : ContDiff ℝ ∞ t) (hu : ContDiff ℝ ∞ u) (L : ℝ) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x = 0 ↔
      coordinateFluxDivergence (metricDivergenceFlux (conformalMatrix g (fun y => -L*t y)) u) x +
        L*fderiv ℝ t x (metricDivergenceFlux (conformalMatrix g (fun y => -L*t y)) u x) = 0 := by
  rw [metricDivergenceFlux_conformal g hp t u L]
  exact coordinateFluxDivergence_exp_depth_zero_iff t (metricDivergenceFlux g u) L x
    (ht.differentiable (by simp) x) ((contDiff_metricDivergenceFlux g hs hp u hu).differentiable (by simp) x)

theorem conformalReferenceMatrix_eq_conformalMatrix (g : MatrixField) (L lam : ℝ) :
    conformalReferenceMatrix g L lam =
      conformalMatrix (fun x => g (lam • x)) (fun x => -L*conformalReferenceCoordinateDepth x) := by
  funext x
  unfold conformalReferenceMatrix conformalMatrix
  congr 2
  ring

theorem actual_reference_original_harmonic_flux_iff (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux (fun y => g (lam • y)) u) x = 0 ↔
      coordinateFluxDivergence (metricDivergenceFlux (conformalReferenceMatrix g L lam) u) x +
        L*fderiv ℝ conformalReferenceCoordinateDepth x
          (metricDivergenceFlux (conformalReferenceMatrix g L lam) u x) = 0 := by
  rw [conformalReferenceMatrix_eq_conformalMatrix]
  have hdil : ContDiff ℝ ∞ (fun y : R3 => lam • y) :=
    (lam • (ContinuousLinearMap.id ℝ R3)).contDiff
  exact metricDivergenceFlux_conformal_zero_iff (fun y => g (lam • y))
    (fun i j => (hg.smooth i j).comp hdil)
    (fun y => hg.posDef (lam • y)) conformalReferenceCoordinateDepth u
    contDiff_conformalReferenceCoordinateDepth hu L x
end OAI.AnisotropicCalderon.ConnectionError
