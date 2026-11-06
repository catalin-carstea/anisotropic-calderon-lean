import Calderon.ActualFullAdjointFirstActions
import Calderon.ActualDensityAngularBoundaryAction

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/
EXPANSION-literal-formal-physical-adjoint-definition-v014.md.
Formal expression only; genuine weighted adjunction and finite L2 domain are separate. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

def referenceFormalAdjointPhysicalDensityOperator
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (-(1/2 : ℝ)) :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    referenceLowerFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • u x) z i) y j) -
  (∑ k : Fin 3,
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => (R x * ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j) • u x) y k)) +
  ∑ i : Fin 3,
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => (R x * normalizedSecondDriftFrameJoint g g2 L i (q,x)) • u x) y i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFormalAdjointPhysicalDensityOperator
