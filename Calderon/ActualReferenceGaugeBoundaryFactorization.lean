import Calderon.ActualReferenceGaugeBoundaryJets
import Calderon.ActualReferenceNormalOrderOneFamily

/-! Full upfront: actual-gauge-boundary-jets-author-oct15-v001/
EXPANSION-factorization-positivity-v003.md. Exact native scalar factorization;
original checked normal positivity and SAME positive exponential gauge. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap MetricVolume
  SphereHarmonic NativeBoundaryCoefficientFamilies

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)

theorem referenceGaugeNormalCoefficient_factor
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    referenceGaugeNormalCoefficient g L Φ a (p,z) =
      referenceExponentialGauge g L Φ p z * normalCoefficientFunction a (p,z) := by
  simp only [referenceGaugeNormalCoefficient, normalCoefficientFunction,
    referenceGaugePrincipalCoefficient, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem referenceGaugeTangentCoefficient_factor
    (j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    referenceGaugeTangentCoefficient g L Φ a j (p,z) =
      referenceExponentialGauge g L Φ p z * tangentCoefficientFunction a j (p,z) := by
  change (∑ i : Fin 3, z i*referenceGaugePrincipalCoefficient g L Φ a (p,z) i j) -
      referenceGaugeNormalCoefficient g L Φ a (p,z)*z j =
    referenceExponentialGauge g L Φ p z *
      ((∑ i : Fin 3, z i*a (p,z) i j)-normalCoefficientFunction a (p,z)*z j)
  rw [referenceGaugeNormalCoefficient_factor]
  have hr : (∑ i : Fin 3, z i*referenceGaugePrincipalCoefficient g L Φ a (p,z) i j) =
      referenceExponentialGauge g L Φ p z*(∑ i : Fin 3, z i*a (p,z) i j) := by
    simp only [referenceGaugePrincipalCoefficient,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hr]
  ring

variable (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem referenceGaugeNormalCoefficient_sphere_pos
    (p : ℝ × (R3 × ℝ)) (x : UnitSphere) :
    0 < referenceGaugeNormalCoefficient g L Φ a (p,x.val) := by
  have ha := referenceNormalCoefficientJetsFamily3_sphere_pos
    g L y0 Φ B ε C ρ H a w hData p x
  unfold referenceNormalCoefficientJetsFamily3 at ha
  rw [coefficientValue_commonSupportCoefficientFamily] at ha
  rw [referenceGaugeNormalCoefficient_factor]
  exact mul_pos (referenceExponentialGauge_pos g L Φ p x.val) ha

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficient_factor
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient_factor
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalCoefficient_sphere_pos
