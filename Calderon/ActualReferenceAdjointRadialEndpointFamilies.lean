import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.CompatibleRadialRightComposition
import Calderon.ActualReferenceSharpMidpointRadialTrace
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

attribute [local irreducible] referenceAdjointHighConormalFamily
  referenceAdjointWeakConormalEndpointFamily referenceNormalDriftThreeHalfMultiplierFamily
  referenceNormalDriftHalfMultiplierFamily referenceTangentialAdjointThreeHalfFamily
  referenceTangentialAdjointHalfFamily referenceNormalThreeHalfMultiplierFamily
  referenceNormalHalfMultiplierFamily

lemma referenceAdjointRadialEndpointFamily_high_half_compatibility
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Nh := referenceAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Nl := referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p
  let Bh := referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Bl := referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Th := referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Tl := referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Ah := referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Al := referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hN : Iout.comp Nh = Nl.comp Iin :=
    referenceAdjointConormalEndpointFamily_high_half_compatibility g L y0 Φ B ε C ρ H a w hData
      τ0 hcalc hreg hF hO hD p hOriginal
  have hBeta : Iin.comp Bh = Bl.comp Iin :=
    referenceNormalDriftMultiplier_high_half_compatibility g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hB : Iout.comp (Iin.comp Bh) = (Iout.comp Bl).comp Iin := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T u) hBeta)
  have hTold := referenceTangentialAdjoint_high_half_compatibility g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 p
  have hNotation := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ) (by norm_num) (by norm_num)
  have hNotationComp := congrArg
    (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I.comp Th) hNotation
  have hT : Iout.comp Th = Tl.comp Iin := hNotationComp.symm.trans hTold
  have hA : Iin.comp Ah.inverse = Al.inverse.comp Iin :=
    referenceNormalMultiplier_inverse_high_half_compatibility g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p
  have hGeneric := OAI.AnisotropicCalderon.RadialEndpointCompatibility.compatible_sum_sub_right_composition
    (Xh := SphereSobolev (3/2:ℝ)) (Xl := SphereSobolev (1/2:ℝ))
    (Yh := SphereSobolev (1/2:ℝ)) (Yl := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  exact hGeneric Nh (Iin.comp Bh) Th Nl (Iout.comp Bl) Tl Ah.inverse Al.inverse Iin Iout hN hB hT hA

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointRadialEndpointFamily_high_half_compatibility
