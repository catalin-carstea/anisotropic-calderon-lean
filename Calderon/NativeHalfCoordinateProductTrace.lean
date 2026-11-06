import Calderon.NativeCoordinateEnergyCancellation
import Calderon.NativeHalfSmoothMultiplier
import Calderon.SphereSobolevCoordinateInclusion

/-! Expanded first in EXPANSION-native-H2-coordinate-product-trace-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeHalfSmoothMultiplier

lemma sphereContinuousScalarMulL_coordinateSmoothDatum (k : Fin 3) :
    sphereContinuousScalarMulL (smoothSphereValue (coordinateSmoothDatum k)) =
      sphereCoordinateMulL k := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae
      (smoothSphereValue (coordinateSmoothDatum k)) f,
    sphereCoordinateMul_value_ae k f] with x h1 h2
  exact h1.trans h2.symm

lemma sphereCoordinateMulL_comm_apply (j k : Fin 3) (f : SphereL2) :
    sphereCoordinateMulL j (sphereCoordinateMulL k f) =
      sphereCoordinateMulL k (sphereCoordinateMulL j f) := by
  apply Lp.ext
  filter_upwards [sphereCoordinateMul_value_ae j (sphereCoordinateMulL k f),
    sphereCoordinateMul_value_ae k f,
    sphereCoordinateMul_value_ae k (sphereCoordinateMulL j f),
    sphereCoordinateMul_value_ae j f] with x h1 h2 h3 h4
  change sphereCoordinateMul j (sphereCoordinateMulL k f) x =
    sphereCoordinateMul k (sphereCoordinateMulL j f) x
  rw [h1,h3]
  change sphereCoordinate j x * sphereCoordinateMul k f x =
    sphereCoordinate k x * sphereCoordinateMul j f x
  rw [h2,h4]
  ring

lemma sphereSobolevCoordinateMul_comm_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : 0 ≤ s)
    (j k : Fin 3) (f : SphereSobolev s) :
    sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1)
      (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single k 1) f) =
    sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single k 1)
      (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1) f) := by
  let I := sphereSobolevInclusionL s 0 hs
  let Z := sphereSobolevZeroEquiv hO hD
  let v := Z.symm (I f)
  have hf : I f = Z v := (Z.apply_symm_apply (I f)).symm
  apply sphereSobolevInclusionL_injective s 0 hs
  simp only [sphereSobolevInclusionL_linearCoordinateMul]
  change sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1)
      (sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single k 1) (I f)) =
    sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single k 1)
      (sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1) (I f))
  rw [hf]
  dsimp only [Z]
  simp only [sphereSobolevLinearCoordinateMulL_zeroEquiv,sphereLinearCoordinateMulL_single]
  exact congrArg Z (sphereCoordinateMulL_comm_apply j k v)

lemma nativeHalfTraceL_coordinate_product
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (u : BallH1) :
    nativeHalfTraceL hF hO hD τ0
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg u) =
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single k 1)
      (nativeHalfTraceL hF hO hD τ0 u) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  let C : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single k 1)
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  have ht (v : BallH1) : I (T v) = Z (τ0.valueTraceL v) :=
    sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 v
  have hmTrace : τ0.valueTraceL (S u) = sphereCoordinateMulL k (τ0.valueTraceL u) := by
    dsimp only [S]
    rw [valueTraceL_contDiffSMulL,sphereContinuousScalarMulL_coordinateSmoothDatum]
  have hc : I (C (T u)) = Z (sphereCoordinateMulL k (τ0.valueTraceL u)) := by
    have hc := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD
      (1/2 : ℝ) (by norm_num) (EuclideanSpace.single k 1) (T u) (τ0.valueTraceL u) (ht u)
    simpa only [sphereLinearCoordinateMulL_single] using hc
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  change I (T (S u)) = I (C (T u))
  exact (ht (S u)).trans ((congrArg Z hmTrace).trans hc.symm)

lemma nativeHalfSmoothMulL_coordinate_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M) :
    nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum k) hM hm hg =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single k 1) := by
  apply ContinuousLinearMap.ext
  intro f
  change nativeHalfTraceL hF hO hD τ0
    (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
      hM hm hg (NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion hF f)) = _
  rw [nativeHalfTraceL_coordinate_product,
    NativeHalfTraceRightInverse.nativeHalfTraceL_harmonicFirstOrderLiftCompletion]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
