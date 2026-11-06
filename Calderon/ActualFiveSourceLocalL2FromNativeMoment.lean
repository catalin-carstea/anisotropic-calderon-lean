import Calderon.ActualReferenceRadiusUniformScaledL2ContinuousOn
import Calderon.ActualCoveredNativeSourceMomentL2

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile SphereHarmonic

/-- The actual five source profiles inherit one local L² bound from the
checked native density moment, with the radius threshold chosen before
source profiles, dilation, density, measure, cutoff, and δ. -/
theorem exists_local_five_source_eLpNorm_le_native_density_moment
    (S : KnownSideSourceData) (L Rstar : ℝ)
    (cover : NativeNormalCover S L)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℕ) (hRstar : 0 < Rstar) (hp : 24 ≤ p) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ) (lam : ℝ)
        (Psi : R3 → SphereSobolev (3/2 : ℝ)),
        ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
        (∀ k : Fin 5, ContinuousOn (fun z : R3 => R1 k (z,lam)-R2 k (z,lam)) cylinder) →
      ∀ (μ : Measure R3) [IsFiniteMeasureOnCompacts μ]
        (chi : R3 → ℝ), Continuous chi →
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (delta : ℝ), 0 < delta →
        (∀ k : Fin 5, ∀ i : Fin cover.count,
          ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            |R2 k (y,lam)-R1 k (y,lam)| ≤
              C * (referenceRadius delta Rstar p L y)^2 *
                ‖(sphereSobolevZeroEquiv hO hD).symm
                  (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) →
      ∀ y ∈ closedBall (0 : R3) 3,
        let r := referenceRadius delta Rstar p L y
        let s := r ^ ((1 : ℝ) / 23)
        r < rho → ball y s ⊆ cylinder →
        ball y s ⊆ closedBall (0 : R3) 3 →
        (∀ z ∈ ball y s, chi z = 1) →
        ∀ k : Fin 5,
        eLpNorm (fun z : R3 => R1 k (z,lam)-R2 k (z,lam)) 2
          (μ.restrict (ball y s)) ≤
          ENNReal.ofReal (((3/2 : ℝ)^p * r)^2) *
            (ENNReal.ofReal C *
              eLpNorm (fun z : R3 => chi z •
                (sphereSobolevZeroEquiv hO hD).symm
                  (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z)))
                2 (μ.restrict cylinder)) := by
  obtain ⟨rho,hrho,hLocal⟩ :=
    exists_local_eLpNorm_at_referenceRadius_interpolationScale_uniform_continuousOn
      L Rstar p hRstar hp
  refine ⟨rho,hrho,?_⟩
  intro R1 R2 lam Psi hPsi hCompact hSource μ hFinite chi hChi C hC delta hDelta hMoment y hy
  dsimp
  intro hrsmall hBallCylinder hBall3 hchi k
  let F : R3 → ℝ := fun z => R1 k (z,lam)-R2 k (z,lam)
  have hMomentF : ∀ i : Fin cover.count,
      ∀ z ∈ cylinder ∩ (cover.packet i).centers,
      |F z| ≤ C * (referenceRadius delta Rstar p L z)^2 *
        ‖(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z))‖ := by
    intro i z hz
    simpa only [F, abs_sub_comm] using hMoment k i z hz
  have hGlobal := memLp_covered_native_source_moment_and_eLpNorm_le
    S L cover hO hD Psi hPsi hCompact μ chi F hChi (hSource k)
    delta Rstar p hDelta hRstar C hC hMomentF
  have hLocalF := hLocal μ chi F (hSource k) delta hDelta y hy
    hrsmall hBallCylinder hBall3 hchi
  dsimp [F] at hLocalF hGlobal
  exact hLocalF.trans (mul_le_mul_of_nonneg_left hGlobal.2 (by positivity))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
