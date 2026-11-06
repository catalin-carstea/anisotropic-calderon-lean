import Calderon.ActualHighMovingBoundaryFamily
import Calderon.ActualHorizontalSobolevConnection

/-! Literal formal Y=-H+Cprimal-GammaTrace; the genuine global integration by parts is
treated separately. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

def referenceHighFullAdjointFirstAction (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (1/2 : ℝ) :=
  -referenceHighHorizontalAction g L q u y i +
    referenceHighMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (u y) -
    (∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) j) j i) •
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)

def referenceLowerFullAdjointFirstAction (q : ℝ) (R : R3 → ℝ)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
  -referenceLowerHorizontalAction g L q v y i +
    referenceLowerMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (v y) -
    (∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) j) j i) •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v y)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighFullAdjointFirstAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerFullAdjointFirstAction
