import Calderon.ActualHighAdjointMovingBoundaryFamilyDefinition

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceJacobiBoundaryCoefficientJets
  referenceJacobiBoundaryThreeHalfCoefficientJets referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily nativeThreeHalfCoefficientMulL
  referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceLowerMovingBoundaryActionFamily referenceLowerMovingBoundaryAction
  referenceHighAdjointJacobiBoundaryCorrection referenceHighAdjointMovingBoundaryAction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g)

attribute [local irreducible] referenceHighAdjointJacobiBoundaryCorrectionFamily

theorem contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible)
    (hp : (t.1,(t.2,R t.2)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun s => referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R s i) t := by
  trace "high adjoint moving smoothness: proof entered"
  let V := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)
  let T : ℝ × R3 → ℝ × (R3 × ℝ) := fun s => (s.1,(s.2,R s.2))
  let Q0 : ℝ × R3 → V := fun s => referenceHighAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (T s) i
  let J0 : ℝ × R3 → V := fun s => referenceHighAdjointJacobiBoundaryCorrectionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (T s) i
  let A0 : ℝ × R3 → V := fun s => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (T s)
  let c : ℝ × R3 → ℝ := fun s => referenceRadiusHorizontalLogDerivative g L s.1 R s.2 i
  trace "high adjoint moving smoothness: typed families"
  have hT : ContDiffAt ℝ ∞ T t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  have hRadius : ContDiffAt ℝ ∞ (fun s : ℝ × R3 => R s.2) t :=
    hR.comp t contDiffAt_snd
  have hInvRadius : ContDiffAt ℝ ∞ (fun s : ℝ × R3 => (R s.2)⁻¹) t := hRadius.inv hr
  have hQ : ContDiffAt ℝ ∞ Q0 t :=
    (contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (T t) i hp).comp t hT
  trace "high adjoint moving smoothness: coordinate family"
  have hJ : ContDiffAt ℝ ∞ J0 t :=
    (contDiffAt_referenceHighAdjointJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg (T t) i hInv hp).comp t hT
  trace "high adjoint moving smoothness: Jacobi family"
  have hA : ContDiffAt ℝ ∞ A0 t :=
    ((contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)).comp t hT
  have hc : ContDiffAt ℝ ∞ c t :=
    contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R t i hR hr
  trace "high adjoint moving smoothness: radial and scalar families"
  have hTotal : ContDiffAt ℝ ∞ (fun s : ℝ × R3 =>
      (R s.2)⁻¹ • Q0 s + R s.2 • J0 s + c s • A0 s) t :=
    ((hInvRadius.smul hQ).add (hRadius.smul hJ)).add (hc.smul hA)
  trace "high adjoint moving smoothness: final typed sum"
  unfold referenceHighAdjointMovingBoundaryActionFamily
  exact hTotal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
