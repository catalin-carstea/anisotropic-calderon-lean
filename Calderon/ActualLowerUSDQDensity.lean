import Calderon.ActualLowerUSDPresentations

/-! Author: GPT-6.1 Sol, author support only.
Before-code: ../dq-density-module-boundary-upfront-v001.md.
Exact definition-only extraction; no commutator graph or analytic bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
  ActualHigherSZeroPhysicalGraph

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "Qout" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q

/-- Exact native first-coefficient/Q commutator with the true test adjoint. -/
def nativeDZeroCommutatorDensity
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪-(nativeB hO hD hF g g2 hg L q dr Ar p j hg2 hdr hAr U).val x,
      (Qout g2 dr Ar p hdr hAr q) V x⟫_ℝ -
    ⟪U.val x,(Qout g2 dr Ar p hdr hAr q)
      (nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j V) x⟫_ℝ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
