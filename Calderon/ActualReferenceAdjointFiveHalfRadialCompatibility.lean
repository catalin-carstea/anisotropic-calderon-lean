import Calderon.ActualReferenceAdjointFiveHalfRadialFamily
import Calderon.ActualReferenceAdjointFiveHalfConormalLower
import Calderon.CompatibleRadialRightComposition
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceAdjointFiveHalfConormalFamily
  referenceAdjointHighConormalFamily referenceNormalDriftFiveHalfMultiplierFamily
  referenceNormalDriftThreeHalfMultiplierFamily referenceTangentialAdjointFiveHalfFamily
  referenceTangentialAdjointThreeHalfFamily referenceNormalFiveHalfMultiplierFamily
  referenceNormalThreeHalfMultiplierFamily

lemma referenceAdjointRadialEndpointFamily_fivehalf_threehalf_compatibility
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Nh := referenceAdjointFiveHalfConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Nl := referenceAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Bh := referenceNormalDriftFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Bl := referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Th := referenceTangentialAdjointFiveHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Tl := referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Ah := referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Al := referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hN : Iout.comp Nh = Nl.comp Iin :=
    sphereSobolevInclusionL_referenceAdjointFiveHalfConormalFamily
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF hO hD p hOriginal
  have hBeta : Iin.comp Bh = Bl.comp Iin :=
    referenceNormalDriftMultiplier_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hB : Iout.comp (Iin.comp Bh) = (Iout.comp Bl).comp Iin := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg Iout (DFunLike.congr_fun hBeta u)
  have hT : Iout.comp Th = Tl.comp Iin :=
    referenceTangentialAdjoint_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hA : Iin.comp Ah.inverse = Al.inverse.comp Iin :=
    sphereSobolevInclusionL_referenceNormalFiveHalfMultiplierFamily_inverse
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hGeneric := OAI.AnisotropicCalderon.RadialEndpointCompatibility.compatible_sum_sub_right_composition
    (Xh := SphereSobolev (5/2:ℝ)) (Xl := SphereSobolev (3/2:ℝ))
    (Yh := SphereSobolev (3/2:ℝ)) (Yl := SphereSobolev (1/2:ℝ))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  exact hGeneric Nh (Iin.comp Bh) Th Nl (Iout.comp Bl) Tl Ah.inverse Al.inverse Iin Iout hN hB hT hA
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
