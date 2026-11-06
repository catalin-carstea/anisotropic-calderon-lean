import Calderon.ActualReferenceRadialInvertibleEndpointCompatibility
import Calderon.ActualReferenceWeakHalfLiftTopology
import Calderon.ActualReferenceStrongRoom
import Calderon.ActualJointReferenceStrongInverse

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
def referenceRadialEndpointInvertibleLocus (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : Set (ℝ × (R3 × ℝ)) :=
  {p | (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible ∧ (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible ∧ (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible}

lemma isOpen_referenceStrongDriftFamily_zero_invertible_set (hcalc : FixedSobolevCalculus) :
    IsOpen {p : ℝ × (R3 × ℝ) | (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible} := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  apply ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
  exact (contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0).continuous

lemma isOpen_referenceWeakDirichletEnergyFamily_invertible_set (hcalc : FixedSobolevCalculus) :
    IsOpen {p : ℝ × (R3 × ℝ) | (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible} := by
  set_option maxSynthPendingDepth 10 in
    exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
      (contDiff_joint_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc).continuous

lemma isOpen_referenceNormalBoundaryMultiplierFamily_invertible_set
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    IsOpen {p : ℝ × (R3 × ℝ) | (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible} := by
  apply ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
  exact (contDiff_referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).continuous

lemma isOpen_referenceRadialEndpointInvertibleLocus (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : IsOpen (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  exact (isOpen_referenceStrongDriftFamily_zero_invertible_set g L y0 Φ B ε C ρ H a w hData hcalc).inter
    ((isOpen_referenceWeakDirichletEnergyFamily_invertible_set g L y0 Φ B ε C ρ H a w hData hcalc).inter
      (isOpen_referenceNormalBoundaryMultiplierFamily_invertible_set g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0))

lemma referenceSharpRadialTraceFamily_lower_compatibility_on_locus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) :=
  referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.2.2 hp.1 hp.2.1

lemma referenceRadialEndpointInvertibleLocus_mem_of_smallDrift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  exact ⟨referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p.1 p.2 lam Lam hUE hs.1,
    isInvertible_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p lam hs,
    referenceNormalBoundaryMultiplierFamily_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p lam Lam hUE⟩

theorem exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ) ⊆ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  obtain ⟨lam,Lam,δ,hlam,hδ,hδρ,hUE,hWeak⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨δ,hδ,hδρ,?_⟩
  intro p hp
  have hUEp : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam :=
    hUE p ⟨hp.1,hp.2.1,(Icc_subset_Icc (neg_le_neg hδρ) hδρ) hp.2.2⟩
  have hy : ‖p.2.1-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
  have hs := hWeak p.1 hp.1 p.2.1 hy p.2.2 (abs_le.mpr hp.2.2)
  exact referenceRadialEndpointInvertibleLocus_mem_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p lam Lam hUEp hs

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialEndpointInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceRadialEndpointInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialTraceFamily_lower_compatibility_on_locus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
