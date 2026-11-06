import Calderon.ActualFiniteGaugeAdjointRadialFamily
import Calderon.ActualReferenceGaugeAdjointIdentity
import Calderon.ActualReferenceAdjointRadialEndpointFamilies
import Calderon.ActualAdjointMovingBoundaryFamilyFoundation

/-! The same genuine adjoint, with no global high K. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

variable {K : Set (ℝ × (R3 × ℝ))}

attribute [local irreducible] referenceFiniteGaugeAdjointRadialFamily
  referenceFiniteHarmonicProductHighRadialFamily referenceGaugeTangentDefectFiniteHighFamily
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
  referenceGaugeTangentEndpointFamily referenceGaugeTangentSecondEndpointFamily
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceFamily referenceLowerRadialEndpointFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  referenceRadialEndpointInvertibleLocus sphereLowerDistributionalTranspose
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevPartialSumL sphereSobolevInclusionL

lemma sphereSobolevInclusionL_referenceFiniteGaugeAdjointRadialFamily
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,r)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ lam/4)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hG : (q,(y,r)) ∈ G.parameterRoom) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteGaugeAdjointRadialFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q (q,(y,r)) f) =
    referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
          (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let x := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let v := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.productJets 3 Q p)
    (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let Cg := referenceFiniteHarmonicProductHighRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (G.productJets 3 Q p) p f
  let Ug := referenceGaugeTangentDefectFiniteHighFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p f
  let F3 := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p
  let F2 := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  let PH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3
  let P := referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let PN := referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let A := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let S := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Sadj := referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let T := referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let T2 := referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let Tdef := T2-sphereLowerDistributionalTranspose T2
  have hFields :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)).IsInvertible ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible ∧
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible := by
    simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using hp
  have hProduct : v = G.threeHalfMultiplier hcalc hF hO hD τ0 p x :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) =>
      Z (sphereSobolevPartialSum (3/2 : ℝ) n f))
      (G.nativeThreeHalfCoefficientMulL_productJets hcalc hF hO hD τ0 Q p)
  have hReciprocal := referenceGaugeNormalReciprocalRoom_native_inverse_graph
    g L Φ y0 B ε C ρ H a w hData hg G hcalc hF hO hD τ0 p hG
  have hInput : I v = P.inverse (I x) :=
    (congrArg I hProduct).trans
      ((congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Z x)
        (G.high_half_compatibility hcalc hF hO hD τ0 p)).trans
        (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Z (I x))
          hReciprocal.1.symm))
  have hPInv : P (I v) = I x :=
    (congrArg P hInput).trans ((referenceGaugeNormalMultiplierFamilies_isInvertible
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).1.self_apply_inverse (I x))
  have hC : I Cg = S v :=
    sphereSobolevInclusionL_referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel n (G.productJets 3 Q p)
        p lam Lam hUE hsmall hFields.2.1 f
  have hSharp : J (S v) = A (I v) :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v)
      (referenceSharpRadialTraceFamily_lower_compatibility_on_locus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
  have hU : J (I Ug) = Tdef (I v) :=
    referenceGaugeTangentDefectFiniteHighFamily_lower_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p f
  have hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2 := by
    funext z
    exact (coefficientValue_referenceGaugeNormalCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg 3 p z).trans
      (coefficientValue_referenceGaugeNormalCoefficientJetsFamily
        g L Φ y0 B ε C ρ H a w hData hg 2 p z).symm
  have hHigh : I (PH Cg) = P (I Cg) := by
    have h := congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Z Cg)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 F3 F2 hCoeff)
    dsimp only [P]
    unfold referenceGaugeNormalHalfMultiplierFamily
    exact h
  have hHalf : J (P (I Cg)) = PN (J (I Cg)) := by
    have h := congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I Cg))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 F2)
    dsimp only [P,PN]
    unfold referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
    exact h
  have hMain : J (I (PH Cg)) = PN (A (I v)) :=
    (congrArg J hHigh).trans (hHalf.trans (congrArg PN ((congrArg J hC).trans hSharp)))
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by
    have hρ : 0 ≤ ρ := (norm_nonneg (y-y0)).trans hy
    linarith
  have hT : T = r^2 • T2 :=
    referenceGaugeTangentEndpointFamily_eq_radius_sq_smul_second
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy2 r
  have hTt : sphereLowerDistributionalTranspose T = r^2 • sphereLowerDistributionalTranspose T2 := by
    have hLinear := sphereLowerDistributionalTransposeL.map_smul (r^2) T2
    have hNamed : sphereLowerDistributionalTranspose (r^2 • T2) =
        r^2 • sphereLowerDistributionalTranspose T2 :=
      (sphereLowerDistributionalTransposeL_apply _).symm.trans
        (hLinear.trans (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ]
          SphereSobolev (-(1/2 : ℝ)) => r^2 • Z) (sphereLowerDistributionalTransposeL_apply T2)))
    exact (congrArg sphereLowerDistributionalTranspose hT).trans hNamed
  have hTan : T (I v)-sphereLowerDistributionalTranspose T (I v) = r^2 • Tdef (I v) := by
    have hOne := congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I v)) hT
    have hTwo := congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I v)) hTt
    exact (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z-t) hOne hTwo).trans (by
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,smul_sub,Tdef])
  have hWeighted : sphereLowerDistributionalTranspose A (P (I v)) =
      PN (A (I v))+T (I v)-sphereLowerDistributionalTranspose T (I v) :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I v))
      (referenceLowerRadialEndpoint_distributionalTranspose_mul_gaugeNormal
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hFields.2.2 hFields.1 hFields.2.1)
  have hWeightedPoint : sphereLowerDistributionalTranspose A (I x) = PN (A (I v))+r^2 • Tdef (I v) :=
    (congrArg (sphereLowerDistributionalTranspose A) hPInv.symm).trans
      (hWeighted.trans ((by abel : PN (A (I v))+T (I v)-sphereLowerDistributionalTranspose T (I v) =
        PN (A (I v))+(T (I v)-sphereLowerDistributionalTranspose T (I v))).trans
        (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => PN (A (I v))+z) hTan)))
  have hAdjoint : J (Sadj x) = sphereLowerDistributionalTranspose A (I x) :=
    (congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z x)
      (referenceAdjointRadialEndpointFamily_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hFields.2.1)).trans
      (congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z (I x))
        (sphereLowerDistributionalTranspose_referenceLowerRadial
          g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hFields.2.1).symm)
  have hPoint : referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p f = PH Cg+r^2 • Ug := by
    simp only [referenceFiniteGaugeAdjointRadialFamily,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,PH,F3,Cg,Ug,p]
  have hLinear : J (I (PH Cg+r^2 • Ug)) = J (I (PH Cg))+r^2 • J (I Ug) := by
    simp only [map_add,map_smul]
  have hTransport : J (I (PH Cg))+r^2 • J (I Ug) = PN (A (I v))+r^2 • Tdef (I v) :=
    congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t) hMain
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r^2 • z) hU)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  exact (congrArg (fun z : SphereSobolev (3/2 : ℝ) => J (I z)) hPoint).trans
    (hLinear.trans (hTransport.trans (hWeightedPoint.symm.trans hAdjoint.symm)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteGaugeAdjointRadialFamily
