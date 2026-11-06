import Calderon.ActualFullAdjointFirstActions
import Calderon.ActualFiniteHighFullAdjointFirstSection
import Calderon.ActualDensityAngularBoundaryAction

/-! Explicit Hhalf section, not an assumed output image or adjunction statement. -/
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

def referenceFiniteHalfFormalAdjointPhysicalSection
    (g2 : MatrixField) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (1/2 : ℝ) :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => referenceFiniteHighFullAdjointFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
        (fun x => (R x * referenceDensityPrincipalFrameCoefficient g g2 L q x i j) • u x) z i) y j) -
  (∑ k : Fin 3,
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n
        ((R z * ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q z i j *
            referenceFrameConnectionCoefficient g L q z (referenceMetricGramFrame g L (q,z) i) k j) • u z)) y k) +
  ∑ i : Fin 3,
    referenceHighFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n
        ((R z * normalizedSecondDriftFrameJoint g g2 L i (q,z)) • u z)) y i

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHalfFormalAdjointPhysicalSection
