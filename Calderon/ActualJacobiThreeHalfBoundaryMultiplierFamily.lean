import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.ActualJacobiBoundaryMultiplierFamily
import Calderon.NativeThreeHalfBoundaryMultiplierLocalSmoothness

/-! Repackages the chosen Jacobi coefficient; actual H3/2 operator norm only. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceJacobiBoundaryThreeHalfCoefficientFamily (i j : Fin 3)
    (p : ℝ × (R3 × ℝ)) : SmoothCoefficientJets 3 :=
  compactCoefficient 3
    (coefficientValue 2
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j p))
    (contDiff_coefficientValue 2 _) (hasCompactSupport_coefficientValue 2 _)

theorem referenceJacobiBoundaryThreeHalfCoefficientFamily_eq
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j p =
      referenceJacobiBoundaryThreeHalfCoefficientJets
        g L y0 Φ B ε C ρ H a w hData hg p.1 p.2.1 p.2.2 i j hInv := by
  let lift : SmoothCoefficientJets 2 → SmoothCoefficientJets 3 := fun F =>
    compactCoefficient 3 (coefficientValue 2 F)
      (contDiff_coefficientValue 2 F) (hasCompactSupport_coefficientValue 2 F)
  exact congrArg lift (referenceJacobiBoundaryCoefficientFamily_eq
    g hg L y0 Φ B ε C ρ H a w hData i j p hInv)

theorem contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j t)) p := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : (ℝ × (R3 × ℝ)) × R3 → ReferenceEndpointVariables :=
    fun t => (t.1.1,(t.1.2,t.2))
  have hT : ContDiff ℝ ∞ T :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  let J : (ℝ × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 :=
    fun t => referenceFramedNormalizedJacobian g L Φ (T t)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).comp hT
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
  apply contDiffAt_nativeThreeHalfCoefficientMulL_of_joint_on_open
    hcalc hF hO hD τ0 f S hS hf
    (referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j) _ p hInv
  intro t ht x
  change coefficientValue 3
    (referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j t) x.val = f (t,x.val)
  rw [referenceJacobiBoundaryThreeHalfCoefficientFamily,coefficientValue_compactCoefficient]
  change smoothSphereValue (coefficientSmoothData
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j t)) x = _
  rw [referenceJacobiBoundaryCoefficientFamily_eq
    g hg L y0 Φ B ε C ρ H a w hData i j t ht,
    smoothSphereValue_referenceJacobiBoundaryCoefficientJets]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryThreeHalfCoefficientFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryThreeHalfCoefficientFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
