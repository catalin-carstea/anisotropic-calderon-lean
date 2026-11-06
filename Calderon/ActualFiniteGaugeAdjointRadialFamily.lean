import Calderon.ActualFiniteHarmonicProductHighRadialGraph
import Calderon.ActualFiniteGaugeTangentDefectHighGraph

/-! Literal normal multiplier after actual finite primal solve. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

variable {K : Set (ℝ × (R3 × ℝ))}

attribute [local irreducible] nativeThreeHalfCoefficientMulL
  referenceFiniteHarmonicProductHighRadialFamily referenceGaugeTangentDefectFiniteHighFamily

def referenceFiniteGaugeAdjointRadialFamily
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p)).comp
      (referenceFiniteHarmonicProductHighRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (G.productJets 3 Q p) p) +
  p.2.2^2 • referenceGaugeTangentDefectFiniteHighFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugeAdjointRadialFamily
