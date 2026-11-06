import Calderon.ActualAngularCoordinateJets
import Calderon.NativeSmoothMultiplierCommonSupportJets
import Calderon.NativeOrderOneCoefficientMultiplierTopology

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SmoothSphereRotation

lemma sphereRotationDerivative_param_eq_fderiv
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (i j : Fin 3) (t : P) (x : R3) :
    sphereRotationDerivative i j (fun y : R3 => m (t,y)) x =
      fderiv ℝ m (t,x) (0,rotationVector i j x) := by
  have hSlice := (hm.differentiable (by simp) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hAt := congrArg (fun A : R3 →L[ℝ] ℝ => A (rotationVector i j x)) hSlice.fderiv
  simpa only [Function.comp_def,sphereRotationDerivative,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply] using hAt

lemma contDiff_sphereRotationDerivative_param
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (i j : Fin 3) (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun z : P × R3 =>
      sphereRotationDerivative i j (fun x => m (z.1,x)) z.2) := by
  have hSmooth : ContDiff ℝ ∞
      (fun z : P × R3 => fderiv ℝ m z (0,rotationVector i j z.2)) :=
    (hm.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const.prodMk ((contDiff_rotationVector i j).comp contDiff_snd))
  have hEq : (fun z : P × R3 =>
      sphereRotationDerivative i j (fun x => m (z.1,x)) z.2) =
      (fun z : P × R3 => fderiv ℝ m z (0,rotationVector i j z.2)) := by
    funext z
    exact sphereRotationDerivative_param_eq_fderiv m hm i j z.1 z.2
  exact hEq.symm ▸ hSmooth

end OAI.AnisotropicCalderon.SmoothSphereRotation

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
open EnergyBridge SphereHarmonic SmoothSphereRotation ActualAngularHighDraft
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

lemma coordinateBump_sphere (x : UnitSphere) : coordinateBump x.val = 1 := by
  have hn : ‖x.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
  have hx : x.val ∈ closedBall (0 : R3) 1 := by
    rw [mem_closedBall, dist_zero_right]
    exact hn.le
  exact coordinateBump.one_of_mem_closedBall hx

/-- `χ(x) · D_{ji}(c_Q)(x)`; the parameter is a dummy. -/
def rotationCoefficient (Q : SmoothCoefficientJets 3) (j i : Fin 3) : ℝ × R3 → ℝ :=
  fun z => coordinateBump z.2 * sphereRotationDerivative j i (coefficientValue 3 Q) z.2

lemma contDiff_rotationCoefficient (Q : SmoothCoefficientJets 3) (j i : Fin 3) :
    ContDiff ℝ ∞ (rotationCoefficient Q j i) :=
  (coordinateBump.contDiff.comp contDiff_snd).mul
    ((contDiff_sphereRotationDerivative j i _ (contDiff_coefficientValue 3 Q)).comp contDiff_snd)

lemma rotationCoefficient_support (Q : SmoothCoefficientJets 3) (j i : Fin 3) :
    ∀ t x, x ∉ closedBall (0 : R3) 2 → rotationCoefficient Q j i (t,x) = 0 := by
  intro t x hx
  have h : ¬ dist x 0 ≤ 2 := hx
  have h0 : coordinateBump x = 0 := coordinateBump.zero_of_le_dist (not_le.mp h).le
  show coordinateBump x * _ = 0
  rw [h0, zero_mul]

/-- Rotation-derivative jets `G_{ji}^Q`, frozen at the dummy parameter 0. -/
def rotationJets (Q : SmoothCoefficientJets 3) (j i : Fin 3) : SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (rotationCoefficient Q j i) (contDiff_rotationCoefficient Q j i)
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _) (rotationCoefficient_support Q j i) 0

lemma rotationJets_lower_sphere (Q : SmoothCoefficientJets 3) (j i : Fin 3) (x : UnitSphere) :
    coefficientValue 2 (smoothMultiplierLowerJets (rotationJets Q j i)) x.val =
      sphereRotationDerivative j i (coefficientValue 2 (smoothMultiplierLowerJets Q)) x.val := by
  rw [coefficientValue_smoothMultiplierLowerJets, coefficientValue_smoothMultiplierLowerJets]
  unfold rotationJets
  rw [coefficientValue_commonSupportCoefficientFamily]
  show coordinateBump x.val * _ = _
  rw [coordinateBump_sphere, one_mul]


variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]

def rotationCoefficientParameter (m : T × R3 → ℝ) (j i : Fin 3) : T × R3 → ℝ :=
  fun z => coordinateBump z.2 *
    sphereRotationDerivative j i (fun x => m (z.1,x)) z.2

lemma contDiff_rotationCoefficientParameter
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (j i : Fin 3) :
    ContDiff ℝ ∞ (rotationCoefficientParameter m j i) :=
  (coordinateBump.contDiff.comp contDiff_snd).mul
    (contDiff_sphereRotationDerivative_param j i m hm)

lemma rotationCoefficientParameter_support (m : T × R3 → ℝ) (j i : Fin 3) :
    ∀ t x, x ∉ closedBall (0 : R3) 2 → rotationCoefficientParameter m j i (t,x) = 0 := by
  intro t x hx
  have h : ¬ dist x 0 ≤ 2 := hx
  have h0 : coordinateBump x = 0 := coordinateBump.zero_of_le_dist (not_le.mp h).le
  show coordinateBump x * _ = 0
  rw [h0,zero_mul]

lemma rotationJets_commonSupport
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (j i : Fin 3) (t : T) :
    rotationJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) j i =
      commonSupportCoefficientFamily 3 (rotationCoefficientParameter m j i)
        (contDiff_rotationCoefficientParameter m hm j i)
        (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
        (rotationCoefficientParameter_support m j i) t := by
  have hValue : coefficientValue 3 (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) =
      fun x : R3 => m (t,x) := by
    funext x
    exact coefficientValue_commonSupportCoefficientFamily 3 m hm Km hKm hmz t x
  apply smoothCoefficientJets_eq_of_coefficientValue_eq 3
  funext x
  simp only [rotationJets,coefficientValue_commonSupportCoefficientFamily,
    rotationCoefficient,rotationCoefficientParameter,hValue]

lemma smoothMultiplierLowerJets_rotationJets_commonSupport
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (j i : Fin 3) (t : T) :
    smoothMultiplierLowerJets
      (rotationJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) j i) =
      commonSupportCoefficientFamily 2 (rotationCoefficientParameter m j i)
        (contDiff_rotationCoefficientParameter m hm j i)
        (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
        (rotationCoefficientParameter_support m j i) t := by
  rw [rotationJets_commonSupport,smoothMultiplierLowerJets_commonSupport]

variable [FiniteDimensional ℝ T]

lemma contDiff_nativeThreeHalfCoefficientMulL_rotationJets_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (j i : Fin 3) :
    ContDiff ℝ ∞ (fun t : T => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (rotationJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) j i)) := by
  have hSmooth := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (rotationCoefficientParameter m j i) (contDiff_rotationCoefficientParameter m hm j i)
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
    (rotationCoefficientParameter_support m j i)
  simpa only [rotationJets_commonSupport] using hSmooth

lemma contDiff_nativeHalfCoefficientMulL_rotationJets_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (j i : Fin 3) :
    ContDiff ℝ ∞ (fun t : T => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets
        (rotationJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) j i))) := by
  have hSmooth := contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (rotationCoefficientParameter m j i) (contDiff_rotationCoefficientParameter m hm j i)
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
    (rotationCoefficientParameter_support m j i)
  simpa only [smoothMultiplierLowerJets_rotationJets_commonSupport] using hSmooth

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
