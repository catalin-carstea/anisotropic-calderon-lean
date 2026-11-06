import Calderon.ActualJacobiSphereSmoothCoefficient
import Calderon.NativeBoundaryMultiplierLocalSmoothness

/-! Upfront: EXPANSION-ActualJacobiBoundaryMultiplierFamily-v001.md. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceJacobiBoundaryCoefficientFamily (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientJets 2 := by
  classical
  exact if hi : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible then
    referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData
      p.1 p.2.1 p.2.2 i j hi
  else 0

theorem referenceJacobiBoundaryCoefficientFamily_eq
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j p =
      referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData
        p.1 p.2.1 p.2.2 i j hi := by
  simp only [referenceJacobiBoundaryCoefficientFamily,dif_pos hi]

theorem contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j t)) p := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : (ℝ × (R3 × ℝ)) × R3 → ReferenceEndpointVariables := fun t => (t.1.1,(t.1.2,t.2))
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  let J : (ℝ × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 :=
    fun t => referenceFramedNormalizedJacobian g L Φ (T t)
  have hJ : ContDiff ℝ ∞ J := (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).comp hT
  let S : Set ((ℝ × (R3 × ℝ)) × R3) := {t | (J t).IsInvertible}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact hJ.continuous.continuousAt.eventually ht.eventually_nhds
  let f : (ℝ × (R3 × ℝ)) × R3 → ℝ :=
    fun t => referenceFramedJacobiVelocityRemainder g L Φ i (T t) j
  have hf : ContDiffOn ℝ ∞ f S := by
    intro t ht
    exact (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt).comp t
      ((contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i (T t) ht).comp t
        hT.contDiffAt)).contDiffWithinAt
  apply contDiffAt_nativeHalfCoefficientMulL_of_joint_on_open hcalc hF hO hD τ0 f S hS hf
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j) _ p hi
  intro t ht x
  rw [referenceJacobiBoundaryCoefficientFamily_eq g hg L y0 Φ B ε C ρ H a w hData i j t ht,
    smoothSphereValue_referenceJacobiBoundaryCoefficientJets]
  rfl

theorem contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j t)) p := by
  have hAdj : ContDiff ℝ ∞ (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      realHalfOperatorAdjointL A) := by
    apply ContinuousLinearMap.contDiff
  exact hAdj.contDiffAt.comp p
    (contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hi)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryCoefficientFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryCoefficientFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
