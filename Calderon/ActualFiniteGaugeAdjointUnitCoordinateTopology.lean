import Calderon.ActualFiniteGaugeAdjointMovingBoundaryFamily
import Calderon.ActualFiniteGaugeAdjointCoordinateTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
DIRECT-MOVING-TOPOLOGY-PROOF-DECOMPOSITION-UPFRONT-v001.md. Exact existing smoothness proof block. -/
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


lemma contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_unit
    (n : ℕ) (i : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) z i) p := by
  let Qone := unitSphereCoefficientJets 3
  let m : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun z => coefficientValue 3 Qone z.2
  let K : Set R3 := tsupport (coefficientValue 3 Qone)
  have hm : ContDiff ℝ ∞ m := (contDiff_coefficientValue 3 Qone).comp contDiff_snd
  have hK : IsCompact K := hasCompactSupport_coefficientValue 3 Qone
  have hz : ∀ p x, x ∉ K → m (p,x)=0 := by
    intro p x hx
    by_contra hn
    exact hx (subset_tsupport (coefficientValue 3 Qone) hn)
  exact contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_of_value_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n i m hm K hK hz
      (fun _ => Qone) (fun _ => rfl) p hi

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_unit
