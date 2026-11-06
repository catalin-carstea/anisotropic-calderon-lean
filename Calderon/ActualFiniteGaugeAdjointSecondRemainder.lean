import Calderon.ActualFiniteGaugeAdjointRadialFamily
import Calderon.SignedTaylorFixedLinearTransport

/-! Actual higher genuine adjoint signed remainder. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referenceFiniteGaugeAdjointSecondRemainderHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteGaugeAdjointSecondRemainderHighOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

attribute [local irreducible] referenceFiniteGaugeAdjointRadialFamily

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  {K : Set (ℝ × (R3 × ℝ))}

def referenceFiniteGaugeAdjointSecondRemainder
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceFiniteGaugeAdjointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q (q,(y,t))) r

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugeAdjointSecondRemainder
