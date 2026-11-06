import Calderon.ActualReferenceLowerRadialEndpoint
import Calderon.NativeH2RadialFromConormal
import Calderon.ActualReferenceSharpBoundaryIdentity
import Calderon.ActualReferenceInvertibleConormalCompatibility
import Calderon.ActualReferenceSharpUpperTrace

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier NativeHarmonicLiftCompletion
  NativeFullSharpHalfTrace NativeNegativeHalfSmoothMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
lemma referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (m : SmoothData)
    (hDataEq : coefficientSmoothData F = m)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg := by
  subst m
  exact nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg

lemma nativeRadialInverse_expression_congr
    (A B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (T S : Fin 3 → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (D : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hA : A = B) (hT : ∀ j, T j = S j)
    (b d : SphereSobolev (1/2 : ℝ)) (hb : b = d)
    (c e : SphereSobolev (-(1/2 : ℝ))) (hc : c = e) :
    A.inverse (c - ∑ j : Fin 3, T j (D j b)) =
      B.inverse (e - ∑ j : Fin 3, S j (D j d)) := by
  have hInv : A.inverse = B.inverse := congrArg
    (fun Q : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Q.inverse) hA
  have hSum : (∑ j : Fin 3, T j (D j b)) = ∑ j : Fin 3, S j (D j d) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (congrArg
      (fun Q : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Q (D j b))
      (hT j)).trans (congrArg (fun x : SphereSobolev (1/2 : ℝ) => S j (D j x)) hb)
  have hSub : c - ∑ j : Fin 3, T j (D j b) = e - ∑ j : Fin 3, S j (D j d) :=
    congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y) hc hSum
  exact congrArg₂
    (fun Q : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      fun v : SphereSobolev (-(1/2 : ℝ)) => Q v) hInv hSub

lemma nativeCoefficient_boundary_radial_conversion_of_bounds
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (A : SmoothCoefficientJets 2)
    (T : Fin 3 → SmoothCoefficientJets 2)
    (hAData : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (hTData : ∀ j, coefficientSmoothData (T j) = boundaryTangentCoefficientData F j)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M)
    {N : Fin 3 → ℝ} (hN : ∀ j, 0 ≤ N j)
    (ht : ∀ j, ∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ N j)
    (hgt : ∀ j, ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ N j)
    (U : BallSobolev 2) (b : SphereSobolev (1/2 : ℝ)) (c : SphereSobolev (-(1/2 : ℝ)))
    (hb : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) = b)
    (hc : c = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).inverse
      (c - ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j)
        (sphereTangentialDerivativeL hF hO hD j b)) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  have hAlphaEq := referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    hcalc hF hO hD τ0 A (boundaryNormalCoefficientData F) hAData hM hm hg
  have hTangentEq (j : Fin 3) := referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    hcalc hF hO hD τ0 (T j) (boundaryTangentCoefficientData F j) (hTData j)
      (hN j) (ht j) (hgt j)
  have hExpr := nativeRadialInverse_expression_congr
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A)
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hg)
    (fun j => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j))
    (fun j => nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
      (hN j) (ht j) (hgt j))
    (sphereTangentialDerivativeL hF hO hD) hAlphaEq hTangentEq
    b (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) hb.symm
    c (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) hc
  exact hExpr.trans (nativeH2_radial_eq_inverse_conormal_sub_tangent
    hcalc hF hO hD τ0 F lam Lam hUE hM hm hg hN ht hgt U)

lemma nativeCoefficient_boundary_radial_conversion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (A : SmoothCoefficientJets 2)
    (T : Fin 3 → SmoothCoefficientJets 2)
    (hAData : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (hTData : ∀ j, coefficientSmoothData (T j) = boundaryTangentCoefficientData F j)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (U : BallSobolev 2) (b : SphereSobolev (1/2 : ℝ)) (c : SphereSobolev (-(1/2 : ℝ)))
    (hb : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) = b)
    (hc : c = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U))) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A).inverse
      (c - ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j)
        (sphereTangentialDerivativeL hF hO hD j b)) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (boundaryNormalCoefficientData F)
  have htBounds (j : Fin 3) : ∃ Nj : ℝ, 0 ≤ Nj ∧
      (∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ Nj) ∧
      ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ Nj :=
    exists_smooth_ball_multiplier_bound (boundaryTangentCoefficientData F j)
  choose N hN ht hgt using htBounds
  exact nativeCoefficient_boundary_radial_conversion_of_bounds
    hcalc hF hO hD τ0 F A T hAData hTData lam Lam hUE hM hm hg hN ht hgt U b c hb hc

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! The same actual retained coefficient `a`, with no parameter-dependent bound choices in the
maps. -/
lemma referenceConormalTraceFamily_joint_coefficient_eq
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 =
      ordinaryConormalTraceL hcalc τ0 (commonSupportMatrixFamily 2 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p) := by
  rfl

lemma referenceLowerRadialEndpointFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (b : SphereSobolev (1/2 : ℝ)) :
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p b =
    (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p b -
        ∑ j : Fin 3, referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j p
          (sphereTangentialDerivativeL hF hO hD j b)) := by
  simp only [referenceLowerRadialEndpointFamily,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply]

lemma referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)))) := by
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p
  let U : BallSobolev 2 := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) lam Lam := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE
  have hTrace : nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U) =
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f := by
    exact nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong f
  have hConormal := referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong hWeak f
  rw [referenceConormalTraceFamily_joint_coefficient_eq g L y0 Φ B ε C ρ H a w hData hcalc τ0 p] at hConormal
  rw [referenceLowerRadialEndpointFamily_apply]
  exact nativeCoefficient_boundary_radial_conversion hcalc hF hO hD τ0 F
    (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (fun j => referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p)
    (coefficientSmoothData_referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
    (fun j => coefficientSmoothData_referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p)
    lam Lam hUEF U
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)
    (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) hTrace hConormal

lemma referenceSharpRadialTraceFamily_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  change sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) = _
  have hTrans := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  calc
    _ = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f)) := hTrans.symm
    _ = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (referenceNativeRadialTraceOperatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 (harmonicLiftCompletion hF f))) := by
      rw [sphereSobolevInclusionL_referenceSharpRadialTraceFamily]
    _ = _ := (referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p lam Lam hUE hStrong hWeak f).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceConormalTraceFamily_joint_coefficient_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialTraceFamily_lower_compatibility
