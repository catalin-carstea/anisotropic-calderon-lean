import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeOrderOneCoefficientMultiplierInverse
import Calderon.ActualReferenceBoundaryCoefficientFamilies
import Calderon.ActualReferencePrincipalGlobalEllipticity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  NativeOrderOneCoefficientMultiplierInverse

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNormalCoefficientJetsFamily3 : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma coefficientValue_referenceNormalCoefficientJetsFamily3_eq (p : ℝ × (R3 × ℝ)) :
    coefficientValue 3 (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) =
      coefficientValue 2 (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p) :=
  coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1) p

lemma nativeH2CoefficientSmoothData_referenceNormalCoefficientJetsFamily3 (p : ℝ × (R3 × ℝ)) :
    nativeH2CoefficientSmoothData (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) =
      boundaryNormalCoefficientData (commonSupportMatrixFamily 2 a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p) := by
  have hSame : nativeH2CoefficientSmoothData
      (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) =
      coefficientSmoothData (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p) :=
    Subtype.ext (coefficientValue_referenceNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData p)
  exact hSame.trans (coefficientSmoothData_referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)

def referenceNormalOrderOneMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  nativeOrderOneCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (coefficientValue_referenceNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalOrderOneMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceNormalOrderOneMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeOrderOneCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma referenceNormalCoefficientJetsFamily3_sphere_pos (p : ℝ × (R3 × ℝ)) (x : UnitSphere) :
    0 < coefficientValue 3 (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) x.val := by
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p
  have hField : coefficientMatrixField 2 F = (fun z => a (p,z)) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic g L y0 Φ B ε C ρ H a w hData p
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam :=
    hField.symm ▸ hUE
  have hValue := congrArg (fun m : SmoothData => m.val x.val)
    (nativeH2CoefficientSmoothData_referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
  have hLiteral : coefficientValue 3
      (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) x.val =
      (boundaryNormalCoefficientData F).val x.val := hValue
  exact lt_of_lt_of_eq (boundaryNormalCoefficientData_pos F lam Lam hUEF x) hLiteral.symm

lemma referenceNormalOrderOneMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (referenceNormalOrderOneMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible :=
  nativeOrderOneCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (coefficientValue_referenceNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalOrderOneMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceNormalOrderOneMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceNormalOrderOneMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).contDiffAt_map_inverse.comp p
      (contDiff_referenceNormalOrderOneMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceNormalCoefficientJetsFamily3_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2CoefficientSmoothData_referenceNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalOrderOneMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalOrderOneMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalCoefficientJetsFamily3_sphere_pos
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalOrderOneMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalOrderOneMultiplierFamily_inverse
