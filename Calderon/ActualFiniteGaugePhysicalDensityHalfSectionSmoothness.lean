import Calderon.ActualFiniteGaugePhysicalDensityHalfSection
import Calderon.ActualDensityPrincipalFrameSmoothness

/-! Actual outer action on uncompressed eta. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection referenceHighDensityFirstAction
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL referenceFiniteGaugePhysicalDensityHalfSection
  referenceStrongDriftFamily referenceFramedNormalizedJacobian referenceRadialEndpointInvertibleLocus

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

theorem contDiffAt_referenceFiniteGaugePhysicalDensityHalfSection
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hHigh : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z => referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u z) y := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) := fun k z =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u z k
  have hη (k : Fin 3) : ContDiffAt ℝ ∞ (η k) y :=
    contDiffAt_referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y k hu hR hr hHigh
  have hIη (k : Fin 3) : ContDiffAt ℝ ∞ (fun z => I (η k z)) y :=
    I.contDiff.contDiffAt.comp y (hη k)
  have hFirst (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun z => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) z i) y :=
    contDiffAt_referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R (η j) y i (hη j) hR hr hInv hp
  have hΓ (i k j : Fin 3) : ContDiffAt ℝ ∞ (fun z => referenceFrameConnectionCoefficient
      g L q z (referenceMetricGramFrame g L (q,z) i) k j) y :=
    (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun z => referenceMetricGramFrame g L (q,z) i)
      (contDiff_referenceMetricGramFrame_slice g hg L q i) k j).contDiffAt
  have hBase : ContDiffAt ℝ ∞ (fun z : R3 => (q,z)) y :=
    contDiffAt_const.prodMk contDiffAt_id
  have hQ (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun z : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q z i j) y :=
    ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).contDiffAt
      (x := (q,y))).comp y hBase
  have hb (i : Fin 3) : ContDiffAt ℝ ∞
      (fun z : R3 => normalizedSecondDriftFrameJoint g g2 L i (q,z)) y :=
    ((contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).contDiffAt
      (x := (q,y))).comp y hBase
  unfold referenceFiniteGaugePhysicalDensityHalfSection
  apply ContDiffAt.smul hR
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro j hj
    apply (hQ i j).smul
    apply (hFirst i j).sub
    apply ContDiffAt.sum
    intro k hk
    exact (hΓ i k j).smul (hIη k)
  · apply ContDiffAt.sum
    intro i hi
    exact (hb i).smul (hIη i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugePhysicalDensityHalfSection
