import Calderon.ActualAdjointHighSmoothMultiplierSignedTaylorGraphCoercivity

set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian
  referenceGaugeNormalHighInvertibleLocus

lemma exists_reference_commonRadius_jacobiHighPhysicalRoom
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d),
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        p ∈ referenceGaugeNormalHighInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc ∧
        ∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
  obtain ⟨lam,Lam,d,_,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d,hd,hdρ,?_⟩
  intro p hp
  have hz := hRoom p hp
  have hHigh : p ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc := by
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hz.2.2.2.1
  exact ⟨hz.2.2.1,hHigh,hz.2.2.2.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_jacobiHighPhysicalRoom
