import Calderon.ActualFiniteGaugeAdjointJacobiCoordinateTopology

/-! Exact actual radius-profile composition. -/
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


lemma contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum_comp_radius
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => ∑ j : Fin 3, referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n
        (E.jets i j (q,(x,R x))) (q,(x,R x)) j) y := by
  let T : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  let B0 : (ℝ × (R3 × ℝ)) → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    fun p => ∑ j : Fin 3, referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j p) p j
  have hT : ContDiffAt ℝ ∞ T y := contDiffAt_const.prodMk (contDiffAt_id.prodMk hR)
  have hB : ContDiffAt ℝ ∞ B0 (T y) :=
    contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n i (T y) hi
  exact hB.comp (f := T) y hT

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_jacobiSum_comp_radius
