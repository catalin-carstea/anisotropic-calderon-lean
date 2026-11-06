import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.CompactRadialTaylorRoom

/-! Literal signed integral remainder of the same actual lower DN curve; the
native first jet is proved. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceLowerRadialEndpointFamily referenceRadialEndpointInvertibleLocus
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  secondTaylorRemainder radialFirstDerivative HasCompactRadialTaylorRoom

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance : CompleteSpace
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

lemma exists_reference_commonRadius_lowerRadialTrace_raw_taylor
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    HasCompactRadialTaylorRoom
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (Icc (0 : ℝ) 1) (closedBall y0 ρ) ρ := by
  let A : (ℝ × (R3 × ℝ)) → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  apply hasCompactRadialTaylorRoom_of_smooth_room A Ω
    (Icc (0 : ℝ) 1) (closedBall y0 ρ) isCompact_Icc (isCompact_closedBall y0 ρ) ρ
  have hRadius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ) ⊆ Ω :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := hRadius
  refine ⟨δ,hδ,hδρ,hRoom,?_⟩
  intro p hp
  have hi := hRoom hp
  change p ∈ referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 at hi
  unfold referenceRadialEndpointInvertibleLocus at hi
  exact contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hi.2.2 hi.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_lowerRadialTrace_raw_taylor
