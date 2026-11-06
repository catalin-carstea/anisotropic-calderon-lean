import Calderon.ActualConstantOneLeadingCovarianceHalf
import Calderon.ActualNativeMovingLocalRemainder
import Calderon.ActualDensityScalarCutoff
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

private lemma scale_covariant_zero
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r c : ℝ) (hr : r ≠ 0) (h : W) (D I : V →L[ℝ] W)
    (a : Fin 3 → V) (j : Fin 3) (gamma : Fin 3 → ℝ)
    (hc : h+c • D (r⁻¹ • a j)-∑ k : Fin 3, gamma k • I (r⁻¹ • a k)=0) :
    r • h+c • D (a j)-∑ k : Fin 3, gamma k • I (a k)=0 := by
  have hD : r • D (r⁻¹ • a j)=D (a j) := by simp only [map_smul,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hI (k : Fin 3) : r • I (r⁻¹ • a k)=I (a k) := by simp only [map_smul,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hHead : r • (c • D (r⁻¹ • a j))=c • D (a j) :=
    (smul_comm r c _).trans (congrArg (fun z => c • z) hD)
  have hSum : (∑ k : Fin 3, r • (gamma k • I (r⁻¹ • a k)))=
      ∑ k : Fin 3, gamma k • I (a k) :=
    Finset.sum_congr rfl (fun k _ => (smul_comm r (gamma k) _).trans (congrArg (fun z => gamma k • z) (hI k)))
  have hs := congrArg (fun z => r • z) hc
  have hExpand : r • (h+c • D (r⁻¹ • a j)-∑ k : Fin 3, gamma k • I (r⁻¹ • a k))=
      r • h+r • (c • D (r⁻¹ • a j))-∑ k : Fin 3, r • (gamma k • I (r⁻¹ • a k)) := by
    simp only [smul_sub,smul_add,Finset.smul_sum]
  have hReplace := congrArg₂ (fun b s : W => r • h+b-s) hHead hSum
  exact hReplace.symm.trans (hExpand.symm.trans (hs.trans (smul_zero r)))

private lemma leading_covariant_decomposition
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r c : ℝ) (h mov gamma a deg corr tail : V)
    (hCov : r • h+c • deg-gamma=0)
    (hMoving : mov=r⁻¹ • a+c • deg+corr+r • tail) :
    r • h+mov-gamma=r⁻¹ • a+corr+r • tail := by
  have hG : r • h+c • deg=gamma := eq_of_sub_eq_zero hCov
  rw [hMoving,←hG]
  abel

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceHighDensityFirstAction
  referenceHighHorizontalAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighAdjointMovingDifferenceQuotient referenceNativeMovingAdjointParametricCorrection
  sphereSobolevAngularCoordinateTransposeL sphereHighHarmonicDerivativeTransposeL
  sphereSobolevInclusionL constantOneFirstRaisingThreeHalf

theorem referenceConstantOneLeadingHighFirstAction_covariant_half_decomposition
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (i j : Fin 3) (hr : R y ≠ 0) :
    let V : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun k z => (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF k
    R y • referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (V j) y i -
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (constantOneFirstRaisingThreeHalf hF k)) =
      (R y)⁻¹ • constantOneDoubleRaisingHalf hF i j +
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ)
          ((q,y),fderiv ℝ R y) i (constantOneFirstRaisingThreeHalf hF j)) +
      R y • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (constantOneFirstRaisingThreeHalf hF j) := by
  intro V
  let aj := constantOneFirstRaisingThreeHalf hF j
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let f := referenceRadiusHorizontalLogDerivative g L q R y i
  let Horiz := referenceHighHorizontalAction g L q (V j) y i
  let Moving := referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j
  have hCov := referenceConstantOneLeadingRadiusAngularAction_covariant_half_cancellation
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy i j hr
  have hScaled := scale_covariant_zero (R y) f hr Horiz (sphereSobolevShiftedDegreeL (3/2:ℝ)) I
    (constantOneFirstRaisingThreeHalf hF) j Gamma hCov
  have hFirst : R y • referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (V j) y i =
      R y • Horiz+Moving aj := by
    delta referenceHighDensityFirstAction
    simp only [V,Moving,Horiz,aj,map_smul,smul_add,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hFactor := DFunLike.congr_fun (referenceAdjointMovingBoundaryActionFamily_differenceQuotient_factorization
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hr).1 aj
  have hAngular : sphereHighHarmonicDerivativeTransposeL hF hO hD i aj = constantOneDoubleRaisingHalf hF i j := by
    have hSame : sphereHighHarmonicDerivativeTransposeL hF hO hD i =
        sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) i := by
      unfold sphereHighHarmonicDerivativeTransposeL sphereSobolevAngularCoordinateTransposeL
      rfl
    exact (DFunLike.congr_fun hSame aj).trans
      (sphereSobolevAngularCoordinateTransposeL_constantOneFirstRaisingThreeHalf hF hO hD i j)
  have hMoving : Moving aj =
      (R y)⁻¹ • constantOneDoubleRaisingHalf hF i j+f • sphereSobolevShiftedDegreeL (3/2:ℝ) aj+
      I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) ((q,y),fderiv ℝ R y) i aj)+
      R y • referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i aj := by
    have hFValue : Moving aj =
        (R y)⁻¹ • sphereHighHarmonicDerivativeTransposeL hF hO hD i aj+f • sphereSobolevShiftedDegreeL (3/2:ℝ) aj+
        I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) ((q,y),fderiv ℝ R y) i aj)+
        R y • referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i aj := by
      simpa only [Moving,f,I,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply] using hFactor
    exact hFValue.trans (congrArg (fun angularValue => (R y)⁻¹ • angularValue+f • sphereSobolevShiftedDegreeL (3/2:ℝ) aj+
      I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) ((q,y),fderiv ℝ R y) i aj)+
      R y • referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i aj) hAngular)
  have hResult := leading_covariant_decomposition (R y) f Horiz (Moving aj)
    (∑ k : Fin 3, Gamma k • I (constantOneFirstRaisingThreeHalf hF k))
    (constantOneDoubleRaisingHalf hF i j) (sphereSobolevShiftedDegreeL (3/2:ℝ) aj)
    (I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) ((q,y),fderiv ℝ R y) i aj))
    (referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i aj) hScaled hMoving
  exact (congrArg (fun z => z-∑ k : Fin 3, Gamma k • I (constantOneFirstRaisingThreeHalf hF k)) hFirst).trans hResult

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
