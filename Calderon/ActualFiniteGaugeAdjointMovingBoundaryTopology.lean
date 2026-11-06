import Calderon.ActualFiniteGaugeAdjointUnitCoordinatePullback
import Calderon.ActualFiniteGaugeAdjointJacobiCoordinatePullback
import Calderon.ActualFiniteGaugeAdjointUnitRadialPullback
import Calderon.WeightedThreeTermCompositionSmoothness
import Calderon.ActualFiniteGaugeAdjointUnitCoordinateTopology
import Calderon.ActualFiniteGaugeAdjointJacobiCoordinateTopology
import Calderon.ActualFiniteGaugeAdjointUnitRadialTopology
import Calderon.ActualFiniteGaugeAdjointMovingBoundaryFamily
import Calderon.ActualFiniteGaugeAdjointCoordinateTopology

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

attribute [local irreducible] referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceFiniteGaugeAdjointCoordinateFamily
  referenceFiniteGaugeAdjointRadialFamily referenceHighAdjointMovingBoundaryActionFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily nativeThreeHalfCoefficientMulL
  sphereSobolevInclusionL referenceStrongDriftFamily
  referenceRadiusHorizontalLogDerivative


variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)


set_option diagnostics true in
lemma contDiffAt_referenceFiniteGaugeAdjointMovingBoundaryFamily
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteGaugeAdjointMovingBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R x i) y := by
  have hA := contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_unit_comp_radius
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n q R y i hR hi
  have hB := contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum_comp_radius
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R y i hR hi
  have hC := contDiffAt_referenceFiniteGaugeAdjointRadialFamily_unit_comp_radius
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n q R y i hR hi
  have hInv : ContDiffAt ℝ ∞ (fun x => (R x)⁻¹) y := hR.inv hr
  have hLog : ContDiffAt ℝ ∞ (fun x => referenceRadiusHorizontalLogDerivative g L q R x i) y :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR hr).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  have hTotal : ContDiffAt ℝ ∞ (fun x =>
      (R x)⁻¹ • referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(x,R x)) i +
      R x • (∑ j : Fin 3, referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j (q,(x,R x))) (q,(x,R x)) j) +
      referenceRadiusHorizontalLogDerivative g L q R x i • referenceFiniteGaugeAdjointRadialFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(x,R x))) y :=
    ((hInv.smul hA).add (hR.smul hB)).add (hLog.smul hC)
  have hPoint (x : R3) : referenceFiniteGaugeAdjointMovingBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R x i =
      (R x)⁻¹ • referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(x,R x)) i +
      R x • (∑ j : Fin 3, referenceFiniteGaugeAdjointCoordinateFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j (q,(x,R x))) (q,(x,R x)) j) +
      referenceRadiusHorizontalLogDerivative g L q R x i • referenceFiniteGaugeAdjointRadialFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(x,R x)) := by
    unfold referenceFiniteGaugeAdjointMovingBoundaryFamily
    rfl
  exact hTotal.congr_of_eventuallyEq (Filter.Eventually.of_forall hPoint)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointMovingBoundaryFamily
