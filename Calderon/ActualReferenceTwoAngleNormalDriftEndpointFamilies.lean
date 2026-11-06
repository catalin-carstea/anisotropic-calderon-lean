import Calderon.ActualReferenceTwoAngleCoefficientJets
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeSupportedAdjointWeakSolution

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-boundary-coefficients-v095.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (iA jA kA lA : Fin 3)

def referenceTwoAngleNormalDriftFunction (q : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) × R3) : ℝ :=
  ∑ i : Fin 3, q.2 i * referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA q i

include hData
lemma contDiff_referenceTwoAngleNormalDriftFunction :
    ContDiff ℝ ∞ (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA) := by
  apply ContDiff.sum
  intro i hi
  exact ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1)

lemma referenceTwoAngleNormalDriftFunction_zero_outside
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA (t,x) = 0 := by
  unfold referenceTwoAngleNormalDriftFunction
  rw [(referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 t x hx]
  simp

def referenceTwoAngleNormalDriftJetsFamily (n : ℕ) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA)
    (contDiff_referenceTwoAngleNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA kA lA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA kA lA) t

lemma coefficientValue_referenceTwoAngleNormalDriftJetsFamily (n : ℕ) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : R3) :
    coefficientValue n (referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA n t) x =
      referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA (t,x) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA)
    (contDiff_referenceTwoAngleNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA kA lA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA kA lA) t x

lemma smoothSphereValue_referenceTwoAngleNormalDriftJetsFamily_eq_native (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    smoothSphereValue (nativeH2CoefficientSmoothData
      (referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t)) =
    nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
      (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)) := by
  ext x
  have hv := coefficientValue_referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t (x : R3)
  change coefficientValue 3 (referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t) (x : R3) = _
  rw [hv]
  simp only [referenceTwoAngleNormalDriftFunction,nativeNormalDriftCoefficient,
    ContinuousMap.sum_apply,ContinuousMap.mul_apply,sphereCoordinate,smoothSphereValue,
    ContinuousMap.coe_mk,nativeSupportedDriftSmoothData]
  rfl

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceTwoAngleNormalDriftThreeHalfMultiplierFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t)

def referenceTwoAngleNormalDriftHalfMultiplierFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 t)

lemma contDiff_referenceTwoAngleNormalDriftThreeHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceTwoAngleNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA)
    (contDiff_referenceTwoAngleNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA kA lA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA kA lA)

lemma contDiff_referenceTwoAngleNormalDriftHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA)
    (contDiff_referenceTwoAngleNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA kA lA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA kA lA)

lemma referenceTwoAngleNormalDriftMultiplier_high_half_compatibility (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceTwoAngleNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t) =
    (referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
    (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
      (referenceTwoAngleNormalDriftFunction g L Φ H w iA jA kA lA)
      (contDiff_referenceTwoAngleNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA kA lA)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceTwoAngleNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA kA lA) t)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftFunction_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceTwoAngleNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceTwoAngleNormalDriftJetsFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalDriftMultiplier_high_half_compatibility
