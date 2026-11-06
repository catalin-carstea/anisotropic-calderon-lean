import Calderon.ActualReferenceRotationAdjointConormalCompatibility
import Calderon.ActualReferenceRotationNormalDriftEndpointFamilies
import Calderon.ActualReferenceRotationTangentialAdjointEndpointFamilies
import Calderon.ActualReferenceRotationNormalEndpointInverseFamilies
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
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3)

def referenceRotationAdjointThreeHalfRadialFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceRotationAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t +
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceRotationNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t) -
    referenceRotationTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t).comp
      (referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).inverse

def referenceRotationAdjointHalfRadialFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF iA jA t +
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t) -
    referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t).comp
      (referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).inverse

lemma contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceRotationAdjointThreeHalfRadialFamily
  exact ((contDiffOn_referenceRotationAdjointHighConormalFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA).add
    (contDiffOn_const.clm_comp (contDiff_referenceRotationNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0).contDiffOn)).sub
      (contDiff_referenceRotationTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0).contDiffOn |>.clm_comp
        (contDiff_referenceRotationNormalThreeHalfMultiplierFamily_inverse g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA).contDiffOn

lemma contDiffOn_referenceRotationAdjointHalfRadialFamily_invertibleLocus :
    ContDiffOn ℝ ∞ (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceRotationAdjointHalfRadialFamily
  exact ((contDiffOn_referenceRotationAdjointWeakConormalEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA).add
    (contDiffOn_const.clm_comp (contDiff_referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0).contDiffOn)).sub
      (contDiff_referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0).contDiffOn |>.clm_comp
        (contDiff_referenceRotationNormalHalfMultiplierFamily_inverse g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA).contDiffOn

attribute [local irreducible] referenceRotationAdjointHighConormalFamily
  referenceRotationAdjointWeakConormalEndpointFamily referenceRotationNormalDriftThreeHalfMultiplierFamily
  referenceRotationNormalDriftHalfMultiplierFamily referenceRotationTangentialAdjointThreeHalfFamily
  referenceRotationTangentialAdjointHalfFamily referenceRotationNormalThreeHalfMultiplierFamily
  referenceRotationNormalHalfMultiplierFamily

lemma referenceRotationAdjointRadialEndpointFamily_high_half_compatibility
    (hreg : FixedDirichletRegularity) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) =
    (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Nh := referenceRotationAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t
  let Nl := referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF iA jA t
  let Bh := referenceRotationNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let Bl := referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let Th := referenceRotationTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let Tl := referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let Ah := referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t
  let Al := referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t
  have hN : Iout.comp Nh = Nl.comp Iin :=
    referenceRotationAdjointConormalEndpointFamily_high_half_compatibility g L y0 Φ B ε C ρ H a w hData
      τ0 hcalc hreg hF hO hD iA jA t hOriginal
  have hBeta : Iin.comp Bh = Bl.comp Iin :=
    referenceRotationNormalDriftMultiplier_high_half_compatibility g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  have hB : Iout.comp (Iin.comp Bh) = (Iout.comp Bl).comp Iin := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg Iout (congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T u) hBeta)
  have hTold := referenceRotationTangentialAdjoint_high_half_compatibility g L y0 Φ B ε C ρ H a w hData iA jA
    hcalc hF hO hD τ0 t
  have hNotation := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ) (by norm_num) (by norm_num)
  have hNotationComp := congrArg
    (fun I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I.comp Th) hNotation
  have hT : Iout.comp Th = Tl.comp Iin := hNotationComp.symm.trans hTold
  have hA : Iin.comp Ah.inverse = Al.inverse.comp Iin :=
    referenceRotationNormalMultiplier_inverse_high_half_compatibility g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA t
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
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointThreeHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointHalfRadialFamily_invertibleLocus

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointRadialEndpointFamily_high_half_compatibility
