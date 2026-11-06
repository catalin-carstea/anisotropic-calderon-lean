import Calderon.ActualFiniteGaugeAdjointUnitRadialTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-MOVING-PULLBACK-DECOMPOSITION-UPFRONT-v001.md. Exact actual radius-profile composition. -/
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


lemma contDiffAt_referenceFiniteGaugeAdjointRadialFamily_unit_comp_radius
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n
        (unitSphereCoefficientJets 3) (q,(x,R x))) y := by
  let T : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  let C0 : (ℝ × (R3 × ℝ)) → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    fun p => referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) p
  have hT : ContDiffAt ℝ ∞ T y := contDiffAt_const.prodMk (contDiffAt_id.prodMk hR)
  have hC : ContDiffAt ℝ ∞ C0 (T y) :=
    contDiffAt_referenceFiniteGaugeAdjointRadialFamily_unit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (T y) hi
  exact hC.comp (f := T) y hT

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointRadialFamily_unit_comp_radius
