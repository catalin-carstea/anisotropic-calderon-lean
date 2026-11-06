import Calderon.ActualReferenceGaugeBoundaryJets
import Calderon.ActualJointReferenceCoefficientData

/-! Full upfront: actual-gauge-boundary-jets-author-oct15-v001/
EXPANSION-coefficient-families-v002.md. Joint smoothness and common-support
native coefficient data for SAME A=m*a. No extension of finite-domain radial jets. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  SphereHarmonic NativeBoundaryCoefficientFamilies

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg

theorem contDiff_referenceRescaledDepth_joint :
    ContDiff ℝ ∞ (fun p : (ℝ × (R3 × ℝ)) × R3 => referenceRescaledDepth g L Φ p.1 p.2) := by
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  exact contDiff_conformalReferenceCoordinateDepth.comp
    (contDiff_parameterFramedScaledEndpoint
      (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1)
      (conformalReferenceGramFrameOperatorJoint g L) hTheta
      (contDiff_conformalReferenceGramFrameOperatorJoint g hg L))

theorem contDiff_referenceExponentialGauge_joint :
    ContDiff ℝ ∞ (fun p : (ℝ × (R3 × ℝ)) × R3 => referenceExponentialGauge g L Φ p.1 p.2) := by
  exact (contDiff_const.mul
    ((contDiff_referenceRescaledDepth_joint g L Φ y0 B ε C ρ H a w hData hg).sub
      (contDiff_conformalReferenceCoordinateDepth.comp contDiff_fst.snd.fst))).exp

theorem contDiff_referenceGaugePrincipalCoefficient :
    ContDiff ℝ ∞ (referenceGaugePrincipalCoefficient g L Φ a) := by
  exact (contDiff_referenceExponentialGauge_joint g L Φ y0 B ε C ρ H a w hData hg).smul
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1

omit hg in
theorem referenceGaugePrincipalCoefficient_support
    (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugePrincipalCoefficient g L Φ a (p,z) = 0 := by
  have ha := (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p z hz
  simp only [referenceGaugePrincipalCoefficient,ha,smul_zero]

theorem contDiff_referenceGaugeNormalCoefficient :
    ContDiff ℝ ∞ (referenceGaugeNormalCoefficient g L Φ a) :=
  contDiff_normalCoefficientFunction (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)

theorem contDiff_referenceGaugeTangentCoefficient (j : Fin 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentCoefficient g L Φ a j) :=
  contDiff_tangentCoefficientFunction (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg) j

omit hg in
theorem referenceGaugeNormalCoefficient_support
    (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugeNormalCoefficient g L Φ a (p,z) = 0 :=
  normalCoefficientFunction_support (referenceGaugePrincipalCoefficient g L Φ a)
    (closedBall (0 : R3) 3)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p z hz

omit hg in
theorem referenceGaugeTangentCoefficient_support
    (j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugeTangentCoefficient g L Φ a j (p,z) = 0 :=
  tangentCoefficientFunction_support (referenceGaugePrincipalCoefficient g L Φ a)
    (closedBall (0 : R3) 3)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) j p z hz

def referenceGaugeNormalCoefficientJetsFamily (n : ℕ) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)

def referenceGaugeTangentCoefficientJetsFamily (n : ℕ) (j : Fin 3) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceGaugeTangentCoefficient g L Φ a j)
    (contDiff_referenceGaugeTangentCoefficient g L Φ y0 B ε C ρ H a w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentCoefficient_support g L Φ y0 B ε C ρ H a w hData j)

theorem coefficientValue_referenceGaugeNormalCoefficientJetsFamily
    (n : ℕ) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (referenceGaugeNormalCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg n p) z =
      referenceGaugeNormalCoefficient g L Φ a (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p z

theorem coefficientValue_referenceGaugeTangentCoefficientJetsFamily
    (n : ℕ) (j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (referenceGaugeTangentCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg n j p) z =
      referenceGaugeTangentCoefficient g L Φ a j (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceGaugeTangentCoefficient g L Φ a j)
    (contDiff_referenceGaugeTangentCoefficient g L Φ y0 B ε C ρ H a w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentCoefficient_support g L Φ y0 B ε C ρ H a w hData j) p z

theorem coefficientSmoothData_referenceGaugeNormalCoefficientJetsFamily
    (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData (referenceGaugeNormalCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg 2 p) =
      boundaryNormalCoefficientData
        (commonSupportMatrixFamily 2 (referenceGaugePrincipalCoefficient g L Φ a)
          (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
          (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p) :=
  coefficientSmoothData_normalCoefficientJetsFamily
    (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p

theorem coefficientSmoothData_referenceGaugeTangentCoefficientJetsFamily
    (j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData (referenceGaugeTangentCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg 2 j p) =
      boundaryTangentCoefficientData
        (commonSupportMatrixFamily 2 (referenceGaugePrincipalCoefficient g L Φ a)
          (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
          (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p) j :=
  coefficientSmoothData_tangentCoefficientJetsFamily
    (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) j p

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceRescaledDepth_joint
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceExponentialGauge_joint
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugePrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugePrincipalCoefficient_support
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeTangentCoefficient
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficient_support
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient_support
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.coefficientValue_referenceGaugeNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.coefficientValue_referenceGaugeTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.coefficientSmoothData_referenceGaugeNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.coefficientSmoothData_referenceGaugeTangentCoefficientJetsFamily
