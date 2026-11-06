import Calderon.NativeGlobalSmoothH1Density
import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.SphereSobolevInclusion
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology Classical
namespace OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
open NativeSmoothSharpTraceCompletion NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
  SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph DirichletFamily EnergyBridge

/-! Smooth density enters as an imported theorem, not as a hypothesis. -/

lemma sum_half_weight_norm_sq_nativeTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (s : Finset ℕ) (u : BallH1) :
    (∑ k ∈ s, (1+(k:ℝ))*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u)‖^2) ≤
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖u‖^2 := by
  have hl : Continuous (fun v : BallH1 =>
      ∑ k ∈ s, (1+(k:ℝ))*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL v)‖^2) := by
    apply continuous_finset_sum
    intro k hk
    exact continuous_const.mul
      (((sphereHarmonicCoordinate hO hD k).continuous.comp τ0.valueTraceL.continuous).norm.pow 2)
  have hr : Continuous (fun v : BallH1 =>
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖v‖^2) :=
    continuous_const.mul (continuous_norm.pow 2)
  refine denseRange_smoothSobolev.induction_on u (isClosed_le hl hr) ?_
  intro f
  have h := sum_half_weight_norm_sq_trace_coordinate_le_div_mass hF hO hD τ0 f s
  have he : ((sphereSurfaceMass*‖τ0.valueTraceL‖^2+1)*‖smoothSobolev f‖^2)/sphereSurfaceMass =
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev f‖^2 := by
    field_simp [sphereSurfaceMass_pos.ne'] <;> ring
  exact h.trans_eq he

lemma memℓp_half_weight_nativeTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) :
    Memℓp (fun k : ℕ => besselWeight (1/2 : ℝ) k •
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u)) 2 := by
  apply memℓp_gen' (C := (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖u‖^2)
  intro s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos (1/2 : ℝ) _),mul_pow,besselWeight_one_half_sq] using
    sum_half_weight_norm_sq_nativeTrace_le hF hO hD τ0 s u

def nativeHalfTrace (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) :
    SphereSobolev (1/2 : ℝ) :=
  ⟨fun k => besselWeight (1/2 : ℝ) k • sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u),
    memℓp_half_weight_nativeTrace hF hO hD τ0 u⟩

lemma sphereSobolevCoefficientL_nativeHalfTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (nativeHalfTrace hF hO hD τ0 u) =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u) := by
  change besselWeight (-(1/2 : ℝ)) k • (besselWeight (1/2 : ℝ) k •
    sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u)) = _
  rw [smul_smul]
  have hw : besselWeight (-(1/2 : ℝ)) k * besselWeight (1/2 : ℝ) k = 1 := by
    simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1+(k:ℝ)) (-(1/2 : ℝ)) (1/2 : ℝ)).symm
  rw [hw,one_smul]

def nativeHalfTraceLinear (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    BallH1 →ₗ[ℝ] SphereSobolev (1/2 : ℝ) where
  toFun := nativeHalfTrace hF hO hD τ0
  map_add' u v := by
    apply sphereSobolev_ext (1/2 : ℝ)
    intro k
    simp only [map_add,sphereSobolevCoefficientL_nativeHalfTrace]
  map_smul' c u := by
    apply sphereSobolev_ext (1/2 : ℝ)
    intro k
    simp only [map_smul,sphereSobolevCoefficientL_nativeHalfTrace,RingHom.id_apply]

def nativeHalfTraceBound (τ0 : UnitBallValueTrace) : ℝ :=
  Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)

lemma norm_sq_nativeHalfTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) :
    ‖nativeHalfTrace hF hO hD τ0 u‖^2 ≤
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖u‖^2 := by
  rw [norm_sq_sphereSobolev]
  simp only [sphereSobolevCoefficientL_nativeHalfTrace,besselWeight_one_half_sq]
  apply Real.tsum_le_of_sum_le
  · intro k
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · intro s
    exact sum_half_weight_norm_sq_nativeTrace_le hF hO hD τ0 s u

lemma norm_nativeHalfTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) :
    ‖nativeHalfTrace hF hO hD τ0 u‖ ≤ nativeHalfTraceBound τ0*‖u‖ := by
  have hC : 0 ≤ ‖τ0.valueTraceL‖^2+1/sphereSurfaceMass :=
    add_nonneg (sq_nonneg _) (div_nonneg zero_le_one sphereSurfaceMass_pos.le)
  have hs : (nativeHalfTraceBound τ0*‖u‖)^2 =
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖u‖^2 := by
    rw [nativeHalfTraceBound,mul_pow,Real.sq_sqrt hC]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  exact (norm_sq_nativeHalfTrace_le hF hO hD τ0 u).trans_eq hs.symm

def nativeHalfTraceL (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfTraceLinear hF hO hD τ0).mkContinuous (nativeHalfTraceBound τ0)
    (norm_nativeHalfTrace_le hF hO hD τ0)

lemma sphereSobolevCoefficientL_nativeHalfTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (nativeHalfTraceL hF hO hD τ0 u) =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL u) :=
  sphereSobolevCoefficientL_nativeHalfTrace hF hO hD τ0 u k

lemma norm_nativeHalfTraceL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ‖nativeHalfTraceL hF hO hD τ0‖ ≤ nativeHalfTraceBound τ0 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  exact norm_nativeHalfTrace_le hF hO hD τ0 u

lemma sphereSobolevInclusionL_nativeHalfTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (nativeHalfTraceL hF hO hD τ0 u) =
      sphereSobolevZeroEquiv hO hD (τ0.valueTraceL u) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_nativeHalfTraceL,
    sphereSobolevCoefficientL_zeroEquiv]

lemma nativeHalfTraceL_smoothSobolev
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) :
    nativeHalfTraceL hF hO hD τ0 (smoothSobolev f) = smoothHalfTrace hF hO hD τ0 f := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_nativeHalfTraceL,sphereSobolevCoefficientL_smoothHalfTrace]

lemma nativeHalfTraceL_zeroDirichlet
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : BallH1Zero) :
    nativeHalfTraceL hF hO hD τ0 (u : BallH1) = 0 := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_nativeHalfTraceL,valueTraceL_zeroDirichlet,map_zero,map_zero]

end OAI.AnisotropicCalderon.NativeFullSharpHalfTrace

#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.sum_half_weight_norm_sq_nativeTrace_le
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.memℓp_half_weight_nativeTrace
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTrace
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.sphereSobolevCoefficientL_nativeHalfTrace
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceLinear
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceBound
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.norm_sq_nativeHalfTrace_le
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.norm_nativeHalfTrace_le
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.sphereSobolevCoefficientL_nativeHalfTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.norm_nativeHalfTraceL_le
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.sphereSobolevInclusionL_nativeHalfTraceL
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL_smoothSobolev
#print axioms OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL_zeroDirichlet
