import Calderon.NativeSmoothSharpTraceFinite
import Calderon.NativeHarmonicH1LiftCompletion
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open NativeSmoothSharpTraceFinite NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
  SphereHarmonic SpectralCoreRegularity DirichletFamily SpectralWeightedGraph
open EnergyBridge

lemma sphereSurfaceMass_pos : 0 < sphereSurfaceMass :=
  measureReal_univ_pos

lemma sum_half_weight_norm_sq_trace_coordinate_le_div_mass
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) (s : Finset ℕ) :
    (∑ k ∈ s,
      (1+(k : ℝ))*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2) ≤
        ((sphereSurfaceMass*‖τ0.valueTraceL‖^2+1)*‖smoothSobolev u‖^2)/sphereSurfaceMass := by
  apply (le_div_iff₀ sphereSurfaceMass_pos).mpr
  rw [mul_comm _ sphereSurfaceMass]
  exact sum_half_weight_norm_sq_trace_coordinate_le hF hO hD τ0 u s

lemma memℓp_half_weight_smoothTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) :
    Memℓp (fun k : ℕ => besselWeight (1/2 : ℝ) k •
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))) 2 := by
  apply memℓp_gen' (C :=
    ((sphereSurfaceMass*‖τ0.valueTraceL‖^2+1)*‖smoothSobolev u‖^2)/sphereSurfaceMass)
  intro s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos (1/2 : ℝ) _),mul_pow,besselWeight_one_half_sq] using
    sum_half_weight_norm_sq_trace_coordinate_le_div_mass hF hO hD τ0 u s

def smoothHalfTrace (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) :
    SphereSobolev (1/2 : ℝ) :=
  ⟨fun k => besselWeight (1/2 : ℝ) k •
    sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u)),
      memℓp_half_weight_smoothTrace hF hO hD τ0 u⟩

lemma sphereSobolevCoefficientL_smoothHalfTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (smoothHalfTrace hF hO hD τ0 u) =
      sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u)) := by
  change besselWeight (-(1/2 : ℝ)) k • (besselWeight (1/2 : ℝ) k •
    sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))) = _
  rw [smul_smul]
  have hw : besselWeight (-(1/2 : ℝ)) k * besselWeight (1/2 : ℝ) k = 1 := by
    simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1+(k:ℝ)) (-(1/2 : ℝ)) (1/2 : ℝ)).symm
  rw [hw,one_smul]

lemma norm_sq_smoothHalfTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) :
    ‖smoothHalfTrace hF hO hD τ0 u‖^2 ≤
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev u‖^2 := by
  rw [norm_sq_sphereSobolev]
  simp only [sphereSobolevCoefficientL_smoothHalfTrace,besselWeight_one_half_sq]
  have h := Real.tsum_le_of_sum_le
    (f := fun k : ℕ => (1+(k:ℝ))*
      ‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2)
    (fun k => mul_nonneg (by positivity) (sq_nonneg _))
    (sum_half_weight_norm_sq_trace_coordinate_le_div_mass hF hO hD τ0 u)
  have he : ((sphereSurfaceMass*‖τ0.valueTraceL‖^2+1)*‖smoothSobolev u‖^2)/sphereSurfaceMass =
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev u‖^2 := by
    field_simp [sphereSurfaceMass_pos.ne'] <;> ring
  exact h.trans_eq he

lemma norm_smoothHalfTrace_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) :
    ‖smoothHalfTrace hF hO hD τ0 u‖ ≤
      Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev u‖ := by
  have hC : 0 ≤ ‖τ0.valueTraceL‖^2+1/sphereSurfaceMass :=
    add_nonneg (sq_nonneg _) (div_nonneg zero_le_one sphereSurfaceMass_pos.le)
  have hs : (Real.sqrt (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev u‖)^2 =
      (‖τ0.valueTraceL‖^2+1/sphereSurfaceMass)*‖smoothSobolev u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [hs]
  exact norm_sq_smoothHalfTrace_le hF hO hD τ0 u

lemma exists_unique_halfTrace_of_smooth
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) :
    ∃! v : SphereSobolev (1/2 : ℝ), ∀ k : ℕ,
      sphereSobolevCoefficientL (1/2 : ℝ) k v =
        sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u)) := by
  refine ⟨smoothHalfTrace hF hO hD τ0 u,
    sphereSobolevCoefficientL_smoothHalfTrace hF hO hD τ0 u, ?_⟩
  intro v hv
  apply sphereSobolev_ext
  intro k
  rw [hv k,sphereSobolevCoefficientL_smoothHalfTrace]

end OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion

#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.sphereSurfaceMass_pos
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.sum_half_weight_norm_sq_trace_coordinate_le_div_mass
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.memℓp_half_weight_smoothTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.smoothHalfTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.sphereSobolevCoefficientL_smoothHalfTrace
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.norm_sq_smoothHalfTrace_le
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.norm_smoothHalfTrace_le
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.exists_unique_halfTrace_of_smooth
