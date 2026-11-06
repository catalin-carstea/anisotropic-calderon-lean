import Calderon.ActualReferenceAdjointFiveHalfConormalFamily
import Calderon.ActualReferenceAdjointFiveHalfLiftLower
import Calderon.ActualReferenceAdjointThreeHalfConormalLower

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Exact old-endpoint compatibility of the SAME full-adjoint D2N family,
pointwise on the established weak inverse locus. -/
theorem sphereSobolevInclusionL_referenceAdjointFiveHalfConormalFamily_apply
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (referenceAdjointFiveHalfConormalFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) =
    referenceAdjointHighConormalFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) := by
  simp only [referenceAdjointFiveHalfConormalFamily,
    referenceAdjointHighConormalFamily, ContinuousLinearMap.comp_apply]
  rw [sphereSobolevInclusionL_referenceAdjointThreeHalfConormalTraceFamily]
  rw [lowerOrder_referenceAdjointFiveHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF hO p hOriginal f]

/-- Operator equality needed by the higher radial graph assembly. -/
theorem sphereSobolevInclusionL_referenceAdjointFiveHalfConormalFamily
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceAdjointFiveHalfConormalFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceAdjointHighConormalFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact sphereSobolevInclusionL_referenceAdjointFiveHalfConormalFamily_apply
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF hO hD p hOriginal f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
