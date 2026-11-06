import Calderon.ActualFiveHalfAdjointMovingInRoom

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

attribute [local irreducible] referenceFiveHalfAdjointJacobiBoundaryInRoom

lemma referenceAdjointMovingBoundaryInRoom_fivehalf_threehalf_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hp : (t.1,(t.2,R t.2)) ∈ K)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (t.1,(t.2,R t.2))).IsInvertible) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceFiveHalfAdjointMovingBoundaryInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R t i) =
    (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hQ := DFunLike.congr_fun
    (referenceAdjointCoordinateBoundaryFamily_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (t.1,(t.2,R t.2)) i hWeak) u
  have hJ := DFunLike.congr_fun
    (referenceAdjointJacobiBoundaryInRoom_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg (t.1,(t.2,R t.2)) i hp hWeak) u
  have hC := DFunLike.congr_fun
    (referenceAdjointRadialEndpointFamily_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (t.1,(t.2,R t.2)) hWeak) u
  simp only [ContinuousLinearMap.comp_apply] at hQ hJ hC
  have hApply := congrArg
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (referenceFiveHalfAdjointMovingBoundaryInRoom_apply
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 R t i u)
  simp only [map_add,map_smul] at hApply
  have hCombined := hApply.trans (congrArg₂ (fun x y : SphereSobolev (1/2:ℝ) => x+y)
    (congrArg₂ (fun x y : SphereSobolev (1/2:ℝ) => x+y)
      (congrArg (fun v : SphereSobolev (1/2:ℝ) => (R t.2)⁻¹ • v) hQ)
      (congrArg (fun v : SphereSobolev (1/2:ℝ) => R t.2 • v) hJ))
    (congrArg (fun v : SphereSobolev (1/2:ℝ) =>
      referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i • v) hC))
  simpa only [ContinuousLinearMap.comp_apply,referenceHighAdjointMovingBoundaryActionFamily,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] using hCombined
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
