import Calderon.ActualReferenceRotationNormalCoefficient
import Calderon.ActualReferenceRotationWeakConormalTopology
import Calderon.SphereSobolevTangentialDerivative

/-! Expanded first in EXPANSION-actual-rotation-lower-radial-dense-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


def referenceRotationTangentCoefficientJetsFamily (i j l : Fin 3) :
    (ℝ × (ℝ × (R3 × ℝ))) → SmoothCoefficientJets 2 :=
  tangentCoefficientJetsFamily (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 l

def referenceRotationTangentBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j l : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j l t)

lemma coefficientSmoothData_referenceRotationNormalJets_eq_boundaryData
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    coefficientSmoothData (referenceRotationNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j t) =
    boundaryNormalCoefficientData
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) :=
  coefficientSmoothData_normalCoefficientJetsFamily (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 t

lemma coefficientSmoothData_referenceRotationTangentJets_eq_boundaryData
    (i j l : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    coefficientSmoothData (referenceRotationTangentCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j l t) =
    boundaryTangentCoefficientData
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) l :=
  coefficientSmoothData_tangentCoefficientJetsFamily (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 l t

lemma contDiff_referenceRotationTangentBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j l : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j l) :=
  contDiff_negativeHalf_tangentCoefficientFamily hcalc hF hO hD τ0
    (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 l

def referenceRotationLowerRadialEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j t).inverse.comp
      (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t -
        ∑ l : Fin 3, (referenceRotationTangentBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j l t).comp
            (sphereTangentialDerivativeL hF hO hD l))

lemma referenceRotationLowerRadialEndpointFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f : SphereSobolev (1/2:ℝ)) :
    referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t f =
    (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j t).inverse
      (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f -
        ∑ l : Fin 3, referenceRotationTangentBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j l t
            (sphereTangentialDerivativeL hF hO hD l f)) := by
  simp only [referenceRotationLowerRadialEndpointFamily,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply]

lemma contDiffAt_referenceRotationLowerRadialEndpointFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hNormal : (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j t).IsInvertible)
    (hWeak : (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) t := by
  have hn := contDiff_referenceRotationNormalBoundaryMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j
  have hinv : ContDiffAt ℝ ∞ (fun z => (referenceRotationNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z).inverse) t :=
    hNormal.contDiffAt_map_inverse.comp t hn.contDiffAt
  have hw := contDiffAt_referenceRotationWeakConormalEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t hWeak
  have ht : ContDiffAt ℝ ∞ (fun z => ∑ l : Fin 3,
      (referenceRotationTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j l z).comp (sphereTangentialDerivativeL hF hO hD l)) t := by
    apply ContDiffAt.sum
    intro l hl
    exact (contDiff_referenceRotationTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j l).contDiffAt.clm_comp
        (contDiffAt_const (c := sphereTangentialDerivativeL hF hO hD l))
  exact hinv.clm_comp (hw.sub ht)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceRotationNormalJets_eq_boundaryData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceRotationTangentJets_eq_boundaryData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationTangentBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationLowerRadialEndpointFamily_of_isInvertible
