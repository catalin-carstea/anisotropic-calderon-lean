import Calderon.ActualHighAdjointStaticCoordinateWordBounds

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualReferenceLocalCoordinateWordJets
  ActualReferenceDDHigherHCoframeJets

lemma exists_referenceHighAdjoint_staticEndpoint_third_coordinate_word_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
    let D : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
      ∀ beta : ℝ, 1 ≤ beta → ∀ i : Fin 3,
        HasCoordinateWordJetBound 3 (fun y => C0 i (q,(y,0))) x M beta 0 ∧
        HasCoordinateWordJetBound 3 (fun y => D (q,(y,0))) x M beta 0 := by
  intro C0 D
  have hStatic := exists_referenceHighAdjoint_staticEndpoint_coordinate_word_bounds
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  rcases hStatic with ⟨d,hd,hdρ,hd1,hOrders⟩
  exact hOrders 3

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighAdjoint_staticEndpoint_third_coordinate_word_bound
