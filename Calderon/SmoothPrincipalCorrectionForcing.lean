import Calderon.NativeSmoothOperatorRealization
import Calderon.TauBoundaryEnergyData

/-! Globally smooth principal matrix, compact jets and actual correction forcing.
No exterior normalization or regularity interface is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Gradient ContDiff Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

def smoothPrincipalCutoffMatrix (k : ℕ) (A : MatrixField) (hA : ContDiff ℝ ∞ A) :
    SmoothCoefficientMatrix k := fun i j =>
  compactCoefficient k (fun x : R3 => unitBallSmoothCutoff x * A x i j)
    (unitBallSmoothCutoff.contDiff.mul (contDiff_pi.mp (contDiff_pi.mp hA i) j))
    (unitBallSmoothCutoff.hasCompactSupport.mul_right)

theorem coefficientValue_smoothPrincipalCutoffMatrix
    (k : ℕ) (A : MatrixField) (hA : ContDiff ℝ ∞ A) (i j : Fin 3) :
    coefficientValue k (smoothPrincipalCutoffMatrix k A hA i j) =
      (fun x : R3 => unitBallSmoothCutoff x * A x i j) :=
  coefficientValue_compactCoefficient k _ _ _

theorem coefficientMatrixField_smoothPrincipalCutoffMatrix
    (k : ℕ) (A : MatrixField) (hA : ContDiff ℝ ∞ A) (x : R3) :
    coefficientMatrixField k (smoothPrincipalCutoffMatrix k A hA) x =
      unitBallSmoothCutoff x • A x := by
  ext i j
  change coefficientValue k (smoothPrincipalCutoffMatrix k A hA i j) x =
    unitBallSmoothCutoff x * A x i j
  exact congrFun (coefficientValue_smoothPrincipalCutoffMatrix k A hA i j) x

theorem coefficientMatrixField_smoothPrincipalCutoffMatrix_eqOn
    (k : ℕ) (A : MatrixField) (hA : ContDiff ℝ ∞ A) :
    EqOn (coefficientMatrixField k (smoothPrincipalCutoffMatrix k A hA))
      (A) (ballOpens : Set R3) := by
  intro x hx
  rw [coefficientMatrixField_smoothPrincipalCutoffMatrix,
    unitBallSmoothCutoff_one_of_mem hx, one_smul]

def smoothPrincipalCorrectionForcing (A : MatrixField) (hA : ContDiff ℝ ∞ A)
    (f : SmoothData) : SmoothData :=
  ⟨fun x : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun y : R3 => A y i j *
        fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i), by
    apply ContDiff.sum
    intro i hi
    apply ContDiff.sum
    intro j hj
    exact (((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      ((f.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)).fderiv_right
        (m := ∞) (by simp)).clm_apply contDiff_const⟩

theorem ordinaryPrincipalL_smoothPrincipalCutoffMatrix_smooth_value_ae
    (hcalc : FixedSobolevCalculus) (A : MatrixField) (hA : ContDiff ℝ ∞ A)
    (s : ℕ) (f : SmoothData) :
    TauCeti.Wkp.value s (ordinaryPrincipalL hcalc s (smoothPrincipalCutoffMatrix (s+2) A hA)
      (smoothBallSobolev (s+2) f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => -(smoothPrincipalCorrectionForcing A hA f).1 x) := by
  have hP := ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc s
    (smoothPrincipalCutoffMatrix (s+2) A hA) f
  filter_upwards [hP, ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hxB
  rw [hx]
  change -(∑ i : Fin 3, ∑ j : Fin 3,
    fderiv ℝ (fun y : R3 => coefficientValue (s+2) (smoothPrincipalCutoffMatrix (s+2) A hA i j) y *
      fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i)) =
    -(∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun y : R3 => A y i j *
        fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i))
  apply congrArg (fun t : ℝ => -t)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hχ : (unitBallSmoothCutoff : R3 → ℝ) =ᶠ[𝓝 x] (fun _ => 1) :=
    unitBallSmoothCutoff_eventuallyEq_one (Metric.ball_subset_closedBall hxB)
  have he : (fun y : R3 => coefficientValue (s+2) (smoothPrincipalCutoffMatrix (s+2) A hA i j) y *
      fderiv ℝ f.1 y (coordinateVector j)) =ᶠ[𝓝 x]
      (fun y : R3 => A y i j * fderiv ℝ f.1 y (coordinateVector j)) := by
    filter_upwards [hχ] with y hy
    have hχy : unitBallSmoothCutoff y = (1 : ℝ) := hy
    have hScalar : unitBallSmoothCutoff y * A y i j =
        A y i j :=
      (congrArg (fun q : ℝ => q * A y i j) hχy).trans (one_mul _)
    have hValue : coefficientValue (s+2) (smoothPrincipalCutoffMatrix (s+2) A hA i j) y =
        A y i j :=
      (congrFun (coefficientValue_smoothPrincipalCutoffMatrix (s+2) A hA i j) y).trans hScalar
    exact congrArg (fun q : ℝ => q * fderiv ℝ f.1 y (coordinateVector j)) hValue
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (coordinateVector i)) he.fderiv_eq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothPrincipalCutoffMatrix
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothPrincipalCutoffMatrix
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_smoothPrincipalCutoffMatrix
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_smoothPrincipalCutoffMatrix_eqOn
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothPrincipalCorrectionForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_smoothPrincipalCutoffMatrix_smooth_value_ae
