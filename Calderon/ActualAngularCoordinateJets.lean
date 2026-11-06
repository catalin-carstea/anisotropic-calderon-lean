import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.ActualAngularHighCancellation
import Calderon.NativeLinearCoordinateMultiplierIdentification
import Calderon.SphereSobolevCoordinateInclusion
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

/-! ## Generic typed finite cancellations and within-jet caps -/

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft

/-! ## Actual setting -/

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

local instance angularHighHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance angularHighNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

/-! ### §2 The fixed coordinate coefficient, chosen once -/

/-- Fixed bump, equal to 1 on the closed unit ball, supported in the ball of radius 2. -/
def coordinateBump : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `m_j(t,x) = χ(x) x_j`; the parameter `t` is a dummy. -/
def coordinateCoefficient (j : Fin 3) : ℝ × R3 → ℝ := fun z => coordinateBump z.2 * z.2 j

lemma contDiff_coordinateCoefficient (j : Fin 3) :
    ContDiff ℝ ∞ (coordinateCoefficient j) :=
  (coordinateBump.contDiff.comp contDiff_snd).mul
    ((contDiff_piLp_apply (p := (2 : ENNReal)) (i := j)).comp contDiff_snd)

lemma coordinateCoefficient_support (j : Fin 3) :
    ∀ t x, x ∉ closedBall (0 : R3) 2 → coordinateCoefficient j (t,x) = 0 := by
  intro t x hx
  have h : ¬ dist x 0 ≤ 2 := hx
  have h0 : coordinateBump x = 0 := coordinateBump.zero_of_le_dist (not_le.mp h).le
  show coordinateBump x * x j = 0
  rw [h0, zero_mul]

lemma coordinateCoefficient_sphere (j : Fin 3) (t : ℝ) (x : UnitSphere) :
    coordinateCoefficient j (t,x.val) = x.val j := by
  have hn : ‖x.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
  have hx : x.val ∈ closedBall (0 : R3) 1 := by
    rw [mem_closedBall, dist_zero_right]
    exact hn.le
  have h1 : coordinateBump x.val = 1 := coordinateBump.one_of_mem_closedBall hx
  show coordinateBump x.val * x.val j = x.val j
  rw [h1, one_mul]

/-- The common-support coordinate jets, frozen at the dummy parameter 0. -/
def coordinateJets (j : Fin 3) : SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (coordinateCoefficient j) (contDiff_coordinateCoefficient j)
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _) (coordinateCoefficient_support j) 0

lemma coordinateJets_sphereValue (j : Fin 3) :
    smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets (coordinateJets j))) =
      ∑ k : Fin 3, (EuclideanSpace.single j (1 : ℝ) k) • sphereCoordinate k := by
  apply ContinuousMap.ext
  intro x
  change coefficientValue 2 (smoothMultiplierLowerJets (coordinateJets j)) x.val = _
  rw [coefficientValue_smoothMultiplierLowerJets]
  unfold coordinateJets
  rw [coefficientValue_commonSupportCoefficientFamily, coordinateCoefficient_sphere]
  simp [sphereCoordinate, EuclideanSpace.single_apply] <;> rfl

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))

lemma coordinateJets_half (j : Fin 3) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets (coordinateJets j)) =
      Ml j :=
  nativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue hcalc hF hO hD τ0 _ _
    (coordinateJets_sphereValue j)

lemma coordinateJets_negativeHalf (j : Fin 3) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (coordinateJets j)) = Mn j :=
  nativeNegativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue hcalc hF hO hD τ0 _ _
    (coordinateJets_sphereValue j)

lemma coordinateJets_threeHalf (j : Fin 3) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (coordinateJets j) = Mh j := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hNative := congrArg (fun A : Hi →L[ℝ] Half => A f)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 (coordinateJets j)
      (smoothMultiplierLowerJets (coordinateJets j))
      (coefficientValue_smoothMultiplierLowerJets (coordinateJets j)).symm)
  have hLinear := sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (EuclideanSpace.single j (1 : ℝ)) f
  simp only [ContinuousLinearMap.comp_apply] at hNative
  rw [hNative, coordinateJets_half hcalc hF hO hD τ0 j]
  exact hLinear.symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
