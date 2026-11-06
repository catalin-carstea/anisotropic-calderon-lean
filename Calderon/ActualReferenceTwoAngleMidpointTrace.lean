import Calderon.ActualReferenceTwoAngleRadialRoom
import Calderon.ActualReferenceTwoAngleMidpointCore
import Calderon.ActualReferenceTwoAngleLowerRadialEndpoint
import Calderon.ActualReferenceSharpMidpointRadialTrace

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-midpoint-v020.md. Actual compatible primal midpoint. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open Filter
open scoped Topology

open SphereHarmonic

lemma contDiffOn_referenceTwoAngleSharpMidpointRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    ContDiffOn ℝ ∞ (referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
      (referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) := by
  have hPair : ContDiffOn ℝ ∞ (referenceTwoAngleRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
      (referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) := by
    intro t ht
    have hOrig := ht.1.2.2
    exact ((contDiffAt_referenceTwoAngleLowerRadialEndpointFamily_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hOrig.2.2 hOrig.2.1).prodMk
      (contDiffAt_referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t ht.2)).contDiffWithinAt
  exact contDiffOn_sphereSobolevCompatibleInterpolationFamily
    (referenceTwoAngleRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (isOpen_referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) hPair

lemma contDiffAt_referenceTwoAngleSharpMidpointRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    ContDiffAt ℝ ∞ (referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) t :=
  (contDiffOn_referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).contDiffAt
    ((isOpen_referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).mem_nhds hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleSharpMidpointRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleSharpMidpointRadialTraceFamily
