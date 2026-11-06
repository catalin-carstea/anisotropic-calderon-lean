import Calderon.ActualReferenceGaugeWeakInverse
import Calderon.ActualReferenceGaugeStrongInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

include hg hData in
theorem referenceRadialEndpointInvertibleLocus_mem_on_actual_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  exact ⟨referenceStrongDriftFamily_zero_isInvertible_on_actual_room
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg q hq y hy r hr,
    referenceWeakDirichletEnergyFamily_isInvertible_on_actual_room
      g hg L y0 Φ B ε C ρ H a w hData hcalc q hq y hy r hr,
    referenceNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))⟩

end OAI.AnisotropicCalderon.ConnectionError
