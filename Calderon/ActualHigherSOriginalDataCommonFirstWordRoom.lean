import Calderon.ActualLowerSSelfFormation
import Calderon.ActualCommonFirstWordQuadraticAdjoint

/-! Original-data specialization of the already native common first-word room producer.
No new room, germ, estimate, norm, or analytic premise is supplied. Source-only
structural repair; all source/API/body/norm/literature37/model holds remain. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSOriginalDataCommonFirstWordRoom
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows
  ActualPiJacobiRadialGainedRows ActualRetainedGeneratorMultiplierGains
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

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

/-- The complete common first-word room on the original endpoint data's germs. -/
theorem exists_common_first_word_room (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ := by
  exact ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
    data.δ0 data.δ0_pos data.germs

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSOriginalDataCommonFirstWordRoom
