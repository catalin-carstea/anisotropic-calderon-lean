import Calderon.NativeH2SmoothMultiplierOutwardTrace
import Calderon.SmoothHalfTraceDense
import Calderon.SphereSobolevOrderOneRotation
import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.NativeCoefficientMultiplierBoundaryDerivative
import Calderon.NativeSmoothHalfRadialTrace
import Calderon.NativeH2ConormalRadialConversion

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/
EXPANSION-rotation-product-v002.md. Genuine smooth trace product followed by density. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap NativeCoefficientBoundaryMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct NativeFullSharpHalfTrace
  NativeSmoothSharpTraceCompletion SmoothSphereRotation SmoothAngularCasimir NativeSmoothHalfRadialTrace

lemma sphereRotationDerivative_mul_smooth (f g : SmoothData) (i j : Fin 3) (x : R3) :
    sphereRotationDerivative i j (f.1*g.1) x =
      f.1 x * sphereRotationDerivative i j g.1 x +
        sphereRotationDerivative i j f.1 x * g.1 x := by
  unfold sphereRotationDerivative
  rw [fderiv_mul (f.2.differentiable (by simp) x) (g.2.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  nativeHalfTraceL smoothHalfTrace sphereSobolevRotationL sphereSobolevInclusionL
  sphereSobolevZeroEquiv sphereContinuousScalarMulL

lemma nativeHalfCoefficientMulL_smoothHalfTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (f : SmoothData) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F (smoothHalfTrace hF hO hD τ0 f) =
      smoothHalfTrace hF hO hD τ0
        ⟨(coefficientSmoothData F).1*f.1,(coefficientSmoothData F).2.mul f.2⟩ := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let mf : SmoothData := coefficientSmoothData F
  let prod : SmoothData := ⟨mf.1*f.1,mf.2.mul f.2⟩
  let M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let C : SphereL2 →L[ℝ] SphereL2 := sphereContinuousScalarMulL (smoothSphereValue mf)
  let v : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)
  let vp : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue prod)
  let u : SphereSobolev (1/2 : ℝ) := smoothHalfTrace hF hO hD τ0 f
  let up : SphereSobolev (1/2 : ℝ) := smoothHalfTrace hF hO hD τ0 prod
  have hInput : I u = Z v :=
    (sphereSobolevInclusionL_smoothHalfTrace hF hO hD τ0 f).trans
      (congrArg Z (τ0.valueTrace_smooth f))
  have hOutput : I up = Z vp :=
    (sphereSobolevInclusionL_smoothHalfTrace hF hO hD τ0 prod).trans
      (congrArg Z (τ0.valueTrace_smooth prod))
  have hValue : I (M u) = Z (C (Z.symm (I u))) :=
    sphereSobolevInclusionL_nativeHalfCoefficientMulL_value hcalc hF hO hD τ0 F u
  have hSub : Z (C (Z.symm (I u))) = Z (C v) :=
    (congrArg (fun z : SphereSobolev 0 => Z (C (Z.symm z))) hInput).trans
      (congrArg (fun w : SphereL2 => Z (C w)) (Z.symm_apply_apply v))
  have hProd : smoothSphereValue mf * smoothSphereValue f = smoothSphereValue prod := by
    ext x
    rfl
  have hMul : C v = vp :=
    (sphereContinuousScalarMulL_toLp (smoothSphereValue mf) (smoothSphereValue f)).trans
      (congrArg (ContinuousMap.toLp 2 sphereProbability ℝ) hProd)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact hValue.trans (hSub.trans ((congrArg Z hMul).trans hOutput.symm))

lemma sphereSobolevInclusionL_half_negative_smoothHalfTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (smoothHalfTrace hF hO hD τ0 f) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD
          ((ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f))) := by
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  have hTrace := sphereSobolevInclusionL_smoothHalfTrace hF hO hD τ0 f
  rw [τ0.valueTrace_smooth] at hTrace
  have hTrans := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      T (smoothHalfTrace hF hO hD τ0 f))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  simp only [ContinuousLinearMap.comp_apply] at hTrans
  exact hTrans.symm.trans (congrArg J hTrace)

lemma sphereSobolevRotationL_nativeCoefficient_product_rule
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 2) (i j : Fin 3)
    (hDerivative : ∀ x : UnitSphere, coefficientValue 2 G x.val =
      sphereRotationDerivative i j (coefficientValue 2 F) x.val) :
    (sphereSobolevRotationL (1/2 : ℝ) i j).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F) =
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (sphereSobolevRotationL (1/2 : ℝ) i j) +
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevRotationL (1/2 : ℝ) i j
  let M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let N (Q : SmoothCoefficientJets 2) :
      SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let C (Q : SmoothCoefficientJets 2) : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData Q))
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := R.comp M
  let B : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (N F).comp R + (N G).comp I
  have hRot (f : SmoothData) :
      R (smoothHalfTrace hF hO hD τ0 f) =
      J (Z ((ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothSphereValue ⟨sphereRotationDerivative i j f.1,
          contDiff_sphereRotationDerivative i j f.1 f.2⟩))) := by
    let rf : SmoothData := ⟨sphereRotationDerivative i j f.1,
      contDiff_sphereRotationDerivative i j f.1 f.2⟩
    let v : SphereL2 := smoothSphereLift rf.1 rf.2
    have hTrace : R (smoothHalfTrace hF hO hD τ0 f) =
        R (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f)) :=
      congrArg R (nativeHalfTraceL_smoothSobolev hF hO hD τ0 f).symm
    have hChecked : R (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f)) =
        sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num) (Z v) :=
      sphereSobolevRotationL_nativeHalfTrace_smooth hF hO hD τ0 f i j
    have hOrder : sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num) = J :=
      sphereSobolevInclusionL_eq_of_target_eq 0 (-1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)
    have hOrderValue : sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num) (Z v) = J (Z v) :=
      congrArg (fun K : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K (Z v)) hOrder
    have hRep : v = (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue rf) := rfl
    exact hTrace.trans (hChecked.trans (hOrderValue.trans
      (congrArg (fun w : SphereL2 => J (Z w)) hRep)))
  have hNeg (Q : SmoothCoefficientJets 2) (v : SphereL2) :
      N Q (J (Z v)) = J (Z (C Q v)) :=
    (nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 Q (Z v)).trans
      (congrArg (fun w : SphereL2 => J (Z (C Q w))) (Z.symm_apply_apply v))
  have hAdd (v w : SphereL2) : J (Z (v+w)) = J (Z v) + J (Z w) :=
    (congrArg J (Z.map_add v w)).trans (J.map_add (Z v) (Z w))
  have hEq : (A : SphereSobolev (1/2 : ℝ) → SphereSobolev (-(1/2 : ℝ))) = B := by
    apply (denseRange_smoothHalfTrace hF hO hD τ0).equalizer A.continuous B.continuous
    funext f
    let mf : SmoothData := coefficientSmoothData F
    let mg : SmoothData := coefficientSmoothData G
    let prod : SmoothData := ⟨mf.1*f.1,mf.2.mul f.2⟩
    let rf : SmoothData := ⟨sphereRotationDerivative i j f.1,
      contDiff_sphereRotationDerivative i j f.1 f.2⟩
    let rp : SmoothData := ⟨sphereRotationDerivative i j prod.1,
      contDiff_sphereRotationDerivative i j prod.1 prod.2⟩
    let u : SphereSobolev (1/2 : ℝ) := smoothHalfTrace hF hO hD τ0 f
    let vf : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)
    let vrf : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue rf)
    let vrp : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue rp)
    have hAApply : A u = R (M u) := rfl
    have hBApply : B u = N F (R u) + N G (I u) := rfl
    have hHalf : M u = smoothHalfTrace hF hO hD τ0 prod :=
      nativeHalfCoefficientMulL_smoothHalfTrace hcalc hF hO hD τ0 F f
    have hRA : A u = J (Z vrp) :=
      hAApply.trans ((congrArg R hHalf).trans (hRot prod))
    have hTermF : N F (R u) = J (Z (C F vrf)) :=
      (congrArg (N F) (hRot f)).trans (hNeg F vrf)
    have hTermG : N G (I u) = J (Z (C G vf)) :=
      (congrArg (N G) (sphereSobolevInclusionL_half_negative_smoothHalfTrace hF hO hD τ0 f)).trans
        (hNeg G vf)
    have hRB : B u = J (Z (C F vrf + C G vf)) :=
      hBApply.trans ((congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x+y)
        hTermF hTermG).trans (hAdd (C F vrf) (C G vf)).symm)
    have hSphere : smoothSphereValue rp =
        smoothSphereValue mf * smoothSphereValue rf + smoothSphereValue mg * smoothSphereValue f := by
      ext x
      have hScalar := sphereRotationDerivative_mul_smooth mf f i j x.val
      have hDerivativeValue : sphereRotationDerivative i j mf.1 x.val = mg.1 x.val :=
        (hDerivative x).symm
      exact hScalar.trans (congrArg (fun t : ℝ =>
        mf.1 x.val * sphereRotationDerivative i j f.1 x.val + t*f.1 x.val) hDerivativeValue)
    have hValue : vrp = C F vrf + C G vf :=
      (congrArg (ContinuousMap.toLp 2 sphereProbability ℝ) hSphere).trans
        (((ContinuousMap.toLp 2 sphereProbability ℝ).map_add
          (smoothSphereValue mf * smoothSphereValue rf)
          (smoothSphereValue mg * smoothSphereValue f)).trans
          (congrArg₂ (fun x y : SphereL2 => x+y)
            (sphereContinuousScalarMulL_toLp (smoothSphereValue mf) (smoothSphereValue rf)).symm
            (sphereContinuousScalarMulL_toLp (smoothSphereValue mg) (smoothSphereValue f)).symm))
    exact hRA.trans ((congrArg (fun v : SphereL2 => J (Z v)) hValue).trans hRB.symm)
  exact ContinuousLinearMap.ext (fun u => congrFun hEq u)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereRotationDerivative_mul_smooth
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeHalfCoefficientMulL_smoothHalfTrace
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_half_negative_smoothHalfTrace
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_nativeCoefficient_product_rule
