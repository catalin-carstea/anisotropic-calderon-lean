import Calderon.ActualMixedKernelNativeH3Datum
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint NativePolynomialBulkMoments

def nativeHighDensityOperator
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (v : ℝ × (R3 × ℝ)) : BallSobolev 3 →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (v.2.2 * sphereSurfaceMass) •
    (NativeH3CoefficientConormalTrace.nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0
      (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data 3 v)).comp
      (strongHarmonicProjectionL 1 (ordinaryPrincipalL hcalc 1
        (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data 3 v)) - ContinuousLinearMap.id ℝ (BallSobolev 3))

theorem nativeHighDensityOperator_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 3) (v : ℝ × (R3 × ℝ)) :
    nativeHighDensityOperator hcalc hF hO hD τ0 S L P v (E v) =
      referencePhysicalGaugeConormalDensity S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hF hO hD τ0 E v := by
  simp only [nativeHighDensityOperator,referencePhysicalGaugeConormalDensity,
    nativePrincipalHarmonicConormalDensity,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]

theorem contDiff_nativeHighDensityOperator
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ContDiff ℝ ∞ (nativeHighDensityOperator hcalc hF hO hD τ0 S L P) := by
  let F := referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data 3
  let A := fun v => ordinaryPrincipalL hcalc 1 (F v)
  have hA : ContDiff ℝ ∞ A := contDiff_referencePhysicalGauge_fullPrincipal S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc 1
  have hi : ∀ v ∈ (univ : Set (ℝ × (R3 × ℝ))), ((A v).comp (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible :=
    fun v _ => referencePhysicalGauge_fullPrincipal_restriction_isInvertible S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg 1 v
  have hP : ContDiff ℝ ∞ (fun v => strongHarmonicProjectionL 1 (A v)) :=
    contDiffOn_univ.mp (contDiffOn_strongHarmonicProjectionL 1 A univ hA.contDiffOn hi)
  have hC := contDiff_referencePhysicalGauge_nativeThreeHalfConormal S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hF hO hD τ0
  exact (contDiff_snd.snd.mul contDiff_const).smul (hC.clm_comp (hP.sub contDiff_const))

attribute [local irreducible] nativeHighDensityOperator

theorem exists_uniform_nativeHighDensityOperator_profile_firstJet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : (ℝ × (R3 × ℝ)) → BallSobolev 3,
      ∀ v ∈ Q, DifferentiableAt ℝ E v → ∀ M : ℝ, 0 ≤ M → ‖E v‖ ≤ M → ‖fderiv ℝ E v‖ ≤ M →
      ‖nativeHighDensityOperator hcalc hF hO hD τ0 S L P v (E v)‖ ≤ C*M ∧
      ‖fderiv ℝ (fun w => nativeHighDensityOperator hcalc hF hO hD τ0 S L P w (E w)) v‖ ≤ C*M := by
  let A := nativeHighDensityOperator hcalc hF hO hD τ0 S L P
  have hA := contDiff_nativeHighDensityOperator hcalc hreg hF hO hD τ0 S L P
  have hDA : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (m:=∞) (by simp)
  obtain ⟨B,hB⟩ := hQ.exists_bound_of_continuousOn (hA.continuous.prodMk hDA.continuous).continuousOn
  let B0 : ℝ := max B 1
  have hB0 : 0 < B0 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨2*B0,by positivity,?_⟩
  intro E v hv hE M hM hEM hDEM
  have hPair := (hB v hv).trans (le_max_left B 1)
  have hAv : ‖A v‖ ≤ B0 := (show ‖A v‖ ≤ ‖(A v,fderiv ℝ A v)‖ by exact le_max_left _ _).trans hPair
  have hDAv : ‖fderiv ℝ A v‖ ≤ B0 := (show ‖fderiv ℝ A v‖ ≤ ‖(A v,fderiv ℝ A v)‖ by exact le_max_right _ _).trans hPair
  change ‖A v (E v)‖ ≤ 2*B0*M ∧ ‖fderiv ℝ (fun w => A w (E w)) v‖ ≤ 2*B0*M
  constructor
  · exact ((A v).le_opNorm (E v)).trans (by nlinarith only [hAv,hEM,hB0,hM,norm_nonneg (A v)])
  · rw [fderiv_clm_apply (hA.differentiable (by simp) v) hE]
    calc
      _ ≤ ‖(A v).comp (fderiv ℝ E v)‖+‖(fderiv ℝ A v).flip (E v)‖ := norm_add_le _ _
      _ ≤ ‖A v‖*‖fderiv ℝ E v‖+‖(fderiv ℝ A v).flip‖*‖E v‖ := add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) ((fderiv ℝ A v).flip.le_opNorm _)
      _ ≤ B0*M+B0*M := by
        apply add_le_add
        · exact mul_le_mul hAv hDEM (norm_nonneg _) hB0.le
        · exact mul_le_mul (by simpa only [ContinuousLinearMap.opNorm_flip] using hDAv) hEM (norm_nonneg _) hB0.le
      _ = _ := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
