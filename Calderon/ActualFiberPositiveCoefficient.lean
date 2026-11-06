import Calderon.ActualFiberPhysicalCoefficientNormalization
import Calderon.SmoothPositiveCoefficientNativeCoercivity

/-! Actual exp(depth)-weighted principal coefficient; compact derived native coercivity. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referencePhysicalNormalizedPrincipalCoefficient (p : ℝ × (R3 × ℝ)) (z : R3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Real.exp (L*referenceRescaledDepth g L Φ p z) • matrixPrincipalCoefficient H (p,z)

include hg hData in
theorem contDiff_referencePhysicalNormalizedPrincipalCoefficient (p : ℝ × (R3 × ℝ)) :
    ContDiff ℝ ∞ (referencePhysicalNormalizedPrincipalCoefficient g L Φ H p) := by
  let X : R3 → R3 := fun z => referenceFramedPhysicalEndpoint g L Φ (p.1,(p.2,z))
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have ht : ContDiff ℝ ∞ (referenceRescaledDepth g L Φ p) :=
    contDiff_conformalReferenceCoordinateDepth.comp hX
  rcases hData.1 with ⟨_,_,_,_,_,_,hH,hPos,_,_,_,_,_,_,_⟩
  have hPrincipal : ContDiff ℝ ∞ (fun z : R3 => matrixPrincipalCoefficient H (p,z)) :=
    (contDiff_matrixPrincipalCoefficient H hH hPos).comp (contDiff_const.prodMk contDiff_id)
  have hScalar : ContDiff ℝ ∞ (fun z : R3 => L*referenceRescaledDepth g L Φ p z) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => L)).mul ht
  have hExp : ContDiff ℝ ∞ (fun z : R3 => Real.exp (L*referenceRescaledDepth g L Φ p z)) :=
    hScalar.exp
  exact hExp.smul hPrincipal

include hData in
theorem referencePhysicalNormalizedPrincipalCoefficient_posDef
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    (referencePhysicalNormalizedPrincipalCoefficient g L Φ H p z).PosDef := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  exact (matrixPrincipalCoefficient_posDef H hPos (p,z)).smul (Real.exp_pos _)

include hg hData in
theorem memLp_referencePhysicalNormalizedEnergyIntegrand (p : ℝ × (R3 × ℝ)) :
    MemLp (fun z => TauCeti.PDE.energyIntegrand
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H p z)
      ((0 : R3 → R3) z) ((0 : R3 → ℝ) z))
      ⊤ ((volume : Measure R3).restrict ballOpens) :=
  memLp_continuousCoefficientEnergyIntegrand
    (referencePhysicalNormalizedPrincipalCoefficient g L Φ H p)
    (contDiff_referencePhysicalNormalizedPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData p).continuous

include hg hData in
theorem isCoercive_referencePhysicalNormalizedEnergy (p : ℝ × (R3 × ℝ)) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := referencePhysicalNormalizedPrincipalCoefficient g L Φ H p)
      (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
      (memLp_referencePhysicalNormalizedEnergyIntegrand g hg L y0 Φ B ε C ρ H a w hData p)) :=
  isCoercive_continuousPositiveCoefficientEnergy
    (referencePhysicalNormalizedPrincipalCoefficient g L Φ H p)
    (contDiff_referencePhysicalNormalizedPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData p).continuous
    (referencePhysicalNormalizedPrincipalCoefficient_posDef g L y0 Φ B ε C ρ H a w hData p)
    (memLp_referencePhysicalNormalizedEnergyIntegrand g hg L y0 Φ B ε C ρ H a w hData p)

include hg hData in
theorem principalCoefficient_referencePhysicalPullback_eq_radius_smul_normalized
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      |r| • referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) z :=
  principalCoefficient_referencePhysicalPullback_eq
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 z hz

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalNormalizedPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referencePhysicalNormalizedPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalNormalizedPrincipalCoefficient_posDef
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_referencePhysicalNormalizedEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isCoercive_referencePhysicalNormalizedEnergy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.principalCoefficient_referencePhysicalPullback_eq_radius_smul_normalized
