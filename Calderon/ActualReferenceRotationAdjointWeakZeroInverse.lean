import Calderon.ActualReferenceAngleConormalCovariance
import Calderon.ActualReferenceOrthogonalWeakData
import Calderon.NativeZeroEnergyFlipSmoothness
import Calderon.NativeParameterWeakLiftTopology
import Calderon.ActualReferenceRadialEndpointOpenLocus
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible := by
  let e : R3 ≃ₗᵢ[ℝ] R3 := coordinateRotationIsometry i j θ
  let a0 : MatrixField := fun x => a (p,x)
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  let hp := referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p
  have hOrth := referenceOrthogonalNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc e p hOriginal
  have hNative : (nativeZeroCoefficientEnergyL (orthogonalPrincipalCoefficient e a0)
      (orthogonalDriftCoefficient e beta) ((0 : R3 → ℝ) ∘ e) hp).IsInvertible :=
    (nativeZeroCoefficientEnergyL_isInvertible_iff (orthogonalPrincipalCoefficient e a0)
      (orthogonalDriftCoefficient e beta) ((0 : R3 → ℝ) ∘ e) hp).mpr hOrth
  have hA : orthogonalPrincipalCoefficient e a0 =
      (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) :=
    (funext (coordinateRotationPrincipalFamily_eq_orthogonal i j a θ p)).symm
  have hB : orthogonalDriftCoefficient e beta =
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x)) :=
    (funext (coordinateRotationDriftFamily_eq_orthogonal i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) θ p)).symm
  have hCoeff := nativeZeroCoefficientEnergyL_congr_coefficients_for_angle
    (orthogonalPrincipalCoefficient e a0) (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x))
    (orthogonalDriftCoefficient e beta)
    (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x))
    ((0 : R3 → ℝ) ∘ e) 0 hp
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j (θ,p)) hA hB rfl
  have hActual := referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)
  exact Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible)
    (hCoeff.trans hActual.symm)) hNative

def referenceRotationAdjointWeakZeroEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).flip

lemma contDiff_referenceRotationAdjointWeakZeroEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) :=
  contDiff_nativeZeroEnergyFlipFamily
    (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationWeakDirichletEnergyFamily_as_family g L y0 Φ B ε C ρ H a w hData hcalc i j)

lemma referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible :=
  isInvertible_nativeZeroEnergyFlip _
    (referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j θ p hOriginal)

lemma contDiffOn_referenceRotationAdjointNativeWeakInverse_originalLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) => nativeZeroFunctionalInverse
      (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro t ht
  exact (contDiffAt_nativeParameterNativeZeroFunctionalInverse
    (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) t
    (contDiff_referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt
    (referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 ht.2.2.1)).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakZeroEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointWeakZeroEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointNativeWeakInverse_originalLocus
