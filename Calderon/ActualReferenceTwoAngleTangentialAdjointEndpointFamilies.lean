import Calderon.ActualReferenceTangentialAdjointOrderOne
import Calderon.ActualReferenceTwoAngleCoefficientJets
import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (iA jA kA lA : Fin 3)

def referenceTwoAngleTangentRotationJetsFamily (n : ℕ) (i j : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i j)
    (contDiff_tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentRotationCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i j) t

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceTwoAngleTangentialAdjointThreeHalfFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (3/2:ℝ)
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 i j t)) j i

def referenceTwoAngleTangentialAdjointHalfFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (1/2:ℝ)
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTwoAngleTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 i j t)) j i

lemma contDiff_referenceTwoAngleTangentialAdjointThreeHalfFamily :
    ContDiff ℝ ∞ (referenceTwoAngleTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0) := by
  unfold referenceTwoAngleTangentialAdjointThreeHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i j)
      (contDiff_tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
        (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
        (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i j))).neg

lemma contDiff_referenceTwoAngleTangentialAdjointHalfFamily :
    ContDiff ℝ ∞ (referenceTwoAngleTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0) := by
  unfold referenceTwoAngleTangentialAdjointHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i j)
      (contDiff_tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
        (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
        (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i j))).neg

lemma referenceTwoAngleTangentialAdjoint_high_half_compatibility (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (referenceTwoAngleTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t) =
    (referenceTwoAngleTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  unfold referenceTwoAngleTangentialAdjointThreeHalfFamily referenceTwoAngleTangentialAdjointHalfFamily
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) => T f)
    (nativeCoefficientRotationAdjoint_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
        (tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA) i j)
        (contDiff_tangentRotationCoefficientFunction (referenceTwoAnglePrincipalFamily a iA jA kA lA)
          (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 i j)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (tangentRotationCoefficientFunction_support (referenceTwoAnglePrincipalFamily a iA jA kA lA) (closedBall (0 : R3) 3)
          (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 i j) t) j i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentRotationJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentialAdjoint_high_half_compatibility
