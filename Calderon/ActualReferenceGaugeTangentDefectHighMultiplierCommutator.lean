import Calderon.ActualReferenceGaugeTangentHighMultiplierCommutatorGraph
import Calderon.ActualReferenceGaugeTangentDivergenceEndpoints

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-TANGENT-DEFECT-COMMUTATOR-EXPANSION-v001.md. Exact original transpose defect, no raw right-product skew claim. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier SmoothSphereRotation

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceGaugeTangentSecondEndpointFamily
  referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
  referenceGaugeTangentSecondHighMultiplierCommutatorFamily sphereSobolevInclusionL
  sphereLowerDistributionalTranspose nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

lemma referenceGaugeTangentSecondHighMultiplierCommutatorFamily_transpose_defect_inclusion
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    let Q2 := smoothMultiplierLowerJets Q
    let T := referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        ((2 : ℝ) • referenceGaugeTangentSecondHighMultiplierCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p f)) =
    (T-sphereLowerDistributionalTranspose T)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) -
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
      ((T-sphereLowerDistributionalTranspose T)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) := by
  let Q2 := smoothMultiplierLowerJets Q
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let T := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let D := referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
  let c := referenceGaugeTangentSecondHighMultiplierCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p f
  have hCT : J (I c) = T (ML (I f))-MN (T (I f)) :=
    referenceGaugeTangentSecondHighMultiplierCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p f
  have hCompatible : J (ML (I f)) = MN (J (I f)) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I f))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 Q2)
  have hComm (v : SphereSobolev (-(1/2 : ℝ))) : D (MN v) = MN (D v) := by
    dsimp only [D]
    unfold referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
    simp only [ContinuousLinearMap.sum_apply,map_sum]
    exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj =>
      nativeNegativeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRotationDerivativeJetsFamily
          g L y0 Φ B ε C ρ H a w hData hg 2 i j p) Q2 v))
  have hDef (v : SphereSobolev (1/2 : ℝ)) :
      (T-sphereLowerDistributionalTranspose T) v = (2 : ℝ) • T v + D (J v) := by
    have h := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (referenceGaugeTangentSecond_sub_transpose_eq_firstOrder_add_zeroOrder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,two_smul,two_nsmul] using h
  have hExtra : D (J (ML (I f))) = MN (D (J (I f))) :=
    (congrArg D hCompatible).trans (hComm (J (I f)))
  have hMap : MN ((2 : ℝ) • T (I f)+D (J (I f))) =
      (2 : ℝ) • MN (T (I f))+MN (D (J (I f))) :=
    (MN.map_add _ _).trans (congrArg₂
      (fun x y : SphereSobolev (-(1/2 : ℝ)) => x+y) (MN.map_smul 2 (T (I f))) rfl)
  have hGain : (T-sphereLowerDistributionalTranspose T) (ML (I f)) -
      MN ((T-sphereLowerDistributionalTranspose T) (I f)) =
      (2 : ℝ) • (T (ML (I f))-MN (T (I f))) :=
    (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y)
      (hDef (ML (I f))) (congrArg MN (hDef (I f)))).trans
      ((congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y)
        (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (2 : ℝ) • T (ML (I f))+z) hExtra)
        hMap).trans (by simp only [two_smul]; abel))
  have hLinear : J (I ((2 : ℝ) • c)) = (2 : ℝ) • J (I c) := by
    simp only [map_smul]
  exact hLinear.trans ((congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (2 : ℝ) • z) hCT).trans hGain.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondHighMultiplierCommutatorFamily_transpose_defect_inclusion
