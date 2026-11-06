import Calderon.NativeReciprocalGaugeMultipliers
import Calderon.NativeGaugeTestProductEnergy
import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
import Calderon.NativeSmoothOperatorRealization
import Calderon.ActualReferenceWeakEnergyApply
import Calderon.BilinearRotationInvertibility
import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceStrongEnergy
import Calderon.DirichletForcingInjectivity
import Calderon.ActualReferenceWeakDirichletEvaluationReference

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
theorem matrixBilinearForm_eq_inner_matrixOperatorMap
    (A : Matrix (Fin 3) (Fin 3) ℝ) (u v : R3) :
    TauCeti.PDE.matrixBilinearForm A u v = inner ℝ u (matrixOperatorMap A v) := by
  rw [TauCeti.PDE.matrixBilinearForm_apply,EuclideanSpace.inner_eq_star_dotProduct]
  change dotProduct (u : Fin 3 → ℝ) (Matrix.mulVec A (v : Fin 3 → ℝ)) =
    dotProduct (Matrix.mulVec A (v : Fin 3 → ℝ)) (star (u : Fin 3 → ℝ))
  simp only [star_trivial]
  exact dotProduct_comm _ _

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
theorem contDiff_referenceRescaledDepth_slice (p : ℝ × (R3 × ℝ)) :
    ContDiff ℝ ∞ (referenceRescaledDepth g L Φ p) := by
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (Φ v.1 v.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  change ContDiff ℝ ∞ (fun z => conformalReferenceCoordinateDepth
    (referenceFramedPhysicalEndpoint g L Φ (p.1,(p.2,z))))
  exact contDiff_conformalReferenceCoordinateDepth.comp
    ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))

def referenceGaugeScalarJets (k : ℕ) (c : ℝ) (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientJets k :=
  compactCoefficient k
    (fun z => coefficientSpatialBump z * Real.exp (c*referenceRescaledDepth g L Φ p z))
    (coefficientSpatialBump.contDiff.mul
      (contDiff_const.mul (contDiff_referenceRescaledDepth_slice
        g hg L y0 Φ B ε C ρ H a w hData p)).exp)
    (coefficientSpatialBump.hasCompactSupport.mul_right)

theorem coefficientValue_referenceGaugeScalarJets
    (k : ℕ) (c : ℝ) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue k (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData k c p) z =
      coefficientSpatialBump z * Real.exp (c*referenceRescaledDepth g L Φ p z) := by
  exact congrFun (coefficientValue_compactCoefficient k _ _ _) z

theorem coefficientValue_referenceGaugeScalarJets_on_unitBall
    (k : ℕ) (c : ℝ) (p : ℝ × (R3 × ℝ)) (z : R3)
    (hz : z ∈ (ballOpens : Set R3)) :
    coefficientValue k (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData k c p) z =
      Real.exp (c*referenceRescaledDepth g L Φ p z) := by
  rw [coefficientValue_referenceGaugeScalarJets,
    coefficientSpatialBump_eq_one z (by
      change dist z (0 : R3) < 1 at hz
      simpa only [dist_zero_right] using hz.le),one_mul]

theorem referenceGaugeScalarJets_reciprocal
    (k : ℕ) (c : ℝ) (p : ℝ × (R3 × ℝ)) (z : R3)
    (hz : z ∈ (ballOpens : Set R3)) :
    coefficientValue k (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData k c p) z *
      coefficientValue k (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData k (-c) p) z = 1 := by
  rw [coefficientValue_referenceGaugeScalarJets_on_unitBall g hg L y0 Φ B ε C ρ H a w hData k c p z hz,
    coefficientValue_referenceGaugeScalarJets_on_unitBall g hg L y0 Φ B ε C ρ H a w hData k (-c) p z hz,
    ← Real.exp_add]
  convert Real.exp_zero using 1 <;> ring

theorem referenceGaugeScalarMultiplier_isInvertible
    (hcalc : FixedSobolevCalculus) (k : ℕ) (c : ℝ) (p : ℝ × (R3 × ℝ)) :
    (coefficientMultiplier hcalc k
      (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData (k+1) c p)).IsInvertible := by
  apply coefficientMultiplier_isInvertible_of_reciprocal hcalc k _
    (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData (k+1) (-c) p)
  exact referenceGaugeScalarJets_reciprocal g hg L y0 Φ B ε C ρ H a w hData (k+1) c p

theorem referenceGaugeZeroMultiplier_isInvertible
    (hcalc : FixedSobolevCalculus) (c : ℝ) (p : ℝ × (R3 × ℝ)) :
    (nativeCoefficientZeroProductL hcalc
      (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 c p)).IsInvertible := by
  apply nativeCoefficientZeroProductL_isInvertible_of_reciprocal hcalc _
    (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-c) p)
  exact referenceGaugeScalarJets_reciprocal g hg L y0 Φ B ε C ρ H a w hData 2 c p


end OAI.AnisotropicCalderon.ConnectionError
