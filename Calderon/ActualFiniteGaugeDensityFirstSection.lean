import Calderon.ActualFiniteHighHorizontalSection
import Calderon.ActualFiniteGaugeAdjointMovingBoundaryTopology
import Calderon.ActualCovariantDensityFirstActions

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
DIRECT-FINITE-PHYSICAL-DENSITY-DOMAIN-EXPANSION-v001.md. Literal eta, actual uncompressed first outputs. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighHorizontalSection referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAction sphereSobolevInclusionL sphereSobolevPartialSumL nativeThreeHalfCoefficientMulL
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

def referenceFiniteGaugeDensityFirstSection
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) :=
  referenceFiniteHighHorizontalSection g L hcalc hF hO hD τ0 n q u y i +
    referenceFiniteGaugeAdjointMovingBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R y i (u y)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection

lemma contDiffAt_referenceFiniteGaugeDensityFirstSection
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u x i) y := by
  have hHorizontal := contDiffAt_referenceFiniteHighHorizontalSection
    g hg L hcalc hF hO hD τ0 n q u y i hu
  have hMoving := contDiffAt_referenceFiniteGaugeAdjointMovingBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R y i hR hr hi
  unfold referenceFiniteGaugeDensityFirstSection
  exact hHorizontal.add (hMoving.clm_apply hu)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugeDensityFirstSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeDensityFirstSection
