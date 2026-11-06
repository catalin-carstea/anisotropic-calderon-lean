import Calderon.ActualReferenceTwoAngleHighConormalRadialGraph
import Calderon.ActualReferenceTwoAngleConormalHalfDualAdjunction
import Calderon.ActualReferenceTwoAngleAdjointHighRadialFamily
import Calderon.ActualReferenceTwoAngleTangentialHalfDualAdjunction
import Calderon.ActualReferenceSharpMidpointRadialTrace

/-! Two-angle high radial adjunction: the true all-high native pivot pairing. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeCoefficientBoundaryMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceTwoAngleSharpRadialTraceFamily
  referenceTwoAngleAdjointHighConormalFamily referenceTwoAngleHarmonicLiftFamily
  ordinaryConormalTraceL

lemma sphereSobolevDualPairing_referenceTwoAngleHighRadial_adjoint
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j k l t f)) =
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j k l t v)) := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Ah := referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let Al := referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let BN := referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let Mh := referenceTwoAngleNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    i j k l hcalc hF hO hD τ0 t
  let Ml := referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    i j k l hcalc hF hO hD τ0 t
  let Th := referenceTwoAngleTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData
    i j k l hcalc hF hO hD τ0 t
  let Tl := referenceTwoAngleTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData
    i j k l hcalc hF hO hD τ0 t
  let N := referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let Q := referenceTwoAngleAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let S := referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  let z := Ah.inverse v
  let f0 := I f
  let v0 := I v
  let z0 := I z
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let U := referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
    (harmonicLiftCompletion hF f)
  let c := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))
  let T := ∑ d : Fin 3, (referenceTwoAngleTangentBoundaryMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l d t).comp
      (sphereTangentialDerivativeL hF hO hD d)
  have hInv : z0=Al.inverse v0 := congrArg
    (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A v)
    (referenceTwoAngleNormalMultiplier_inverse_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
  have hAZ : Al z0=v0 := (congrArg Al hInv).trans
    ((referenceTwoAngleNormalHalfMultiplierFamily_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).self_apply_inverse v0)
  have hNormal : sphereSobolevDualPairing (1/2:ℝ) z0 (BN (J (S f))) =
      sphereSobolevDualPairing (1/2:ℝ) v0 (J (S f)) :=
    (ContinuousLinearMap.adjoint_inner_right Al z0 (J (S f))).trans
      (congrArg (fun w : SphereSobolev (1/2:ℝ) =>
        sphereSobolevDualPairing (1/2:ℝ) w (J (S f))) hAZ)
  have hFlux : c=BN (J (S f))+T f0 := by
    simpa only [T,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply] using
      referenceTwoAngleHighConormal_negative_eq_normal_add_tangent
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hStrong f
  have hTang : sphereSobolevDualPairing (1/2:ℝ) z0 (T f0)=
      sphereSobolevDualPairing (1/2:ℝ) f0 (Tl z0) :=
    sphereSobolevDualPairing_referenceTwoAngleTangentialLower_adjoint
      g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0 t f0 z0
  have hSum : sphereSobolevDualPairing (1/2:ℝ) z0 (BN (J (S f))+T f0)=
      sphereSobolevDualPairing (1/2:ℝ) z0 (BN (J (S f)))+
        sphereSobolevDualPairing (1/2:ℝ) z0 (T f0) := inner_add_right _ _ _
  have hLeft : sphereSobolevDualPairing (1/2:ℝ) z0 c=
      sphereSobolevDualPairing (1/2:ℝ) v0 (J (S f))+
        sphereSobolevDualPairing (1/2:ℝ) f0 (Tl z0) :=
    (congrArg (fun y : SphereSobolev (-(1/2:ℝ)) =>
      sphereSobolevDualPairing (1/2:ℝ) z0 y) hFlux).trans
        (hSum.trans (congrArg₂ (fun a b : ℝ => a+b) hNormal hTang))
  have hConormal : sphereSobolevDualPairing (1/2:ℝ) z0 c=
      sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z))+
        sphereSobolevDualPairing (1/2:ℝ) f0 (J (Ml z0)) :=
    sphereSobolevDualPairing_referenceTwoAngleH2Conormal_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t hOriginal hStrong f z
  have hB : I (Mh z)=Ml z0 := congrArg
    (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A z)
    (referenceTwoAngleNormalDriftMultiplier_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0 t)
  have hTold := referenceTwoAngleTangentialAdjoint_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData i j k l hcalc hF hO hD τ0 t
  have hNotation := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ) (by norm_num) (by norm_num)
  have hNotationComp := congrArg
    (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A.comp Th) hNotation
  have hTComp : J.comp Th=Tl.comp I := hNotationComp.symm.trans hTold
  have hT : J (Th z)=Tl z0 := congrArg
    (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A z) hTComp
  have hPoint : Q v=N z+I (Mh z)-Th z := by
    simp only [Q,referenceTwoAngleAdjointThreeHalfRadialFamily,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,z,Ah,N,I,Mh,Th]
  have hPointPair := congrArg (fun w : SphereSobolev (1/2:ℝ) =>
    sphereSobolevDualPairing (1/2:ℝ) f0 (J w)) hPoint
  have hDistribute : sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z+I (Mh z)-Th z))=
      sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z))+
        sphereSobolevDualPairing (1/2:ℝ) f0 (J (I (Mh z)))-
          sphereSobolevDualPairing (1/2:ℝ) f0 (J (Th z)) := by
    simp only [map_sub,map_add,sphereSobolevDualPairing,inner_sub_right,inner_add_right]
  have hBP := congrArg (fun w : SphereSobolev (1/2:ℝ) =>
    sphereSobolevDualPairing (1/2:ℝ) f0 (J w)) hB
  have hTP := congrArg (fun w : SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) f0 w) hT
  have hOutput : sphereSobolevDualPairing (1/2:ℝ) f0 (J (Q v))=
      sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z))+
        sphereSobolevDualPairing (1/2:ℝ) f0 (J (Ml z0))-
          sphereSobolevDualPairing (1/2:ℝ) f0 (Tl z0) :=
    hPointPair.trans (hDistribute.trans
      (congrArg₂ (fun a b : ℝ =>
        sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z))+a-b) hBP hTP))
  have hEquation := hLeft.symm.trans hConormal
  have hResult : sphereSobolevDualPairing (1/2:ℝ) v0 (J (S f))=
      sphereSobolevDualPairing (1/2:ℝ) f0 (J (N z))+
        sphereSobolevDualPairing (1/2:ℝ) f0 (J (Ml z0))-
          sphereSobolevDualPairing (1/2:ℝ) f0 (Tl z0) := by linarith only [hEquation]
  exact hResult.trans hOutput.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleHighRadial_adjoint
