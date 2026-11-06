import Calderon.SphereSobolevInclusion
import Calderon.WeightedSourceMomentL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic

theorem memLp_weighted_native_density
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsi : ContDiff ℝ ∞ Psi) (hCompact : HasCompactSupport Psi)
    (μ : Measure R3) [IsFiniteMeasureOnCompacts μ]
    (chi : R3 → ℝ) (hChi : Continuous chi) :
    let w : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
    MemLp (fun y => chi y • w y) 2 μ := by
  have hInclusionCont : Continuous (fun y =>
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) :=
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)).continuous.comp hPsi.continuous
  have hDecodedCont : Continuous (fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) :=
    (sphereSobolevZeroEquiv hO hD).symm.continuous.comp hInclusionCont
  have hInclusionCompact : HasCompactSupport (fun y =>
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) :=
    hCompact.comp_left (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)).map_zero
  have hDecodedCompact : HasCompactSupport (fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) :=
    hInclusionCompact.comp_left (sphereSobolevZeroEquiv hO hD).symm.map_zero
  exact (hChi.smul hDecodedCont).memLp_of_hasCompactSupport hDecodedCompact.smul_left

theorem memLp_weighted_native_source_moment_and_eLpNorm_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsi : ContDiff ℝ ∞ Psi) (hCompact : HasCompactSupport Psi)
    (μ : Measure R3) [IsFiniteMeasureOnCompacts μ]
    (chi : R3 → ℝ) (hChi : Continuous chi) (V r : R3 → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hSourceMeas : AEStronglyMeasurable (fun y => chi y * V y / (r y)^2) μ)
    (hRadius : ∀ᵐ y ∂μ, 0 < r y)
    (hMoment : ∀ᵐ y ∂μ, |V y| ≤ C * (r y)^2 *
      ‖(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) :
    let w : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
    MemLp (fun y => chi y * V y / (r y)^2) 2 μ ∧
      eLpNorm (fun y => chi y * V y / (r y)^2) 2 μ ≤
        ENNReal.ofReal C * eLpNorm (fun y => chi y • w y) 2 μ := by
  exact memLp_weighted_source_moment_and_eLpNorm_le μ chi V r
    (fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)))
    C hC hSourceMeas hRadius hMoment
    (memLp_weighted_native_density hO hD Psi hPsi hCompact μ chi hChi)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
