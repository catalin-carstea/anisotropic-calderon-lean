import Calderon.ActualSameFiveHalfSourceJetWeighted
import Calderon.ActualFiniteCutoffCoreCorrespondence
import Calderon.PositiveSpectralCore

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  WeightedBaseSpectral ReferenceDensityBounds PositiveSpectralCore

lemma sphereSobolevInclusionL_sphereSobolevPartialSumL_fiveHalf
    (n : ℕ) (v : SphereSobolev (5/2 : ℝ)) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (sphereSobolevPartialSumL (5/2 : ℝ) n v) =
    sphereSobolevPartialSumL (3/2 : ℝ) n
      (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) v) := by
  simp only [sphereSobolevPartialSumL_apply, sphereSobolevPartialSum,
    map_sum, sphereSobolevInclusionL_single, sphereSobolevCoefficientL_inclusion]

/-- The existing finite core at order 3/2 is exactly the included H5/2
finite spectral truncation of the same source. -/
theorem finiteCoreSobolevLift_sameFiveHalfPartialSum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U5 : R3 → SphereSobolev (5/2 : ℝ))
    (hU5 : ContDiff ℝ ∞ U5) (hcomp : HasCompactSupport U5)
    (n : ℕ) :
    ∃ F : smoothCompactFiniteSphereCore hO hD,
      (∀ y : R3, finiteCoreSobolevLift hO hD (3/2 : ℝ) F y =
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
          (sphereSobolevPartialSumL (5/2 : ℝ) n (U5 y))) ∧
      tsupport (F : R3 → SphereL2) ⊆ tsupport U5 ∧
      ((∀ y : R3, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (5/2 : ℝ) 0 (by norm_num) (U5 y))) = 0) →
        ∀ y : R3, sphereMean ((F : R3 → SphereL2) y) = 0) := by
  let J : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let u : R3 → SphereSobolev (3/2 : ℝ) := fun y => J (U5 y)
  have hu : ContDiff ℝ ∞ u := J.contDiff.comp hU5
  have hc : HasCompactSupport u := hcomp.comp_left J.map_zero
  let F := finitePartialSumCore hO hD n u hu hc
  refine ⟨F,?_,?_,?_⟩
  · intro y
    calc
      finiteCoreSobolevLift hO hD (3/2 : ℝ) F y =
          sphereSobolevPartialSumL (3/2 : ℝ) n (u y) :=
        finiteCoreSobolevLift_finitePartialSumCore hO hD n u hu hc y
      _ = J (sphereSobolevPartialSumL (5/2 : ℝ) n (U5 y)) :=
        (sphereSobolevInclusionL_sphereSobolevPartialSumL_fiveHalf n (U5 y)).symm
  · apply closure_mono
    intro y hy
    change (F : R3 → SphereL2) y ≠ 0 at hy
    change U5 y ≠ 0
    intro hU0
    have hF0 : (F : R3 → SphereL2) y = 0 := by
      change (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
          (sphereSobolevPartialSumL (3/2 : ℝ) n (u y))) = 0
      simp [u, hU0]
    exact hy hF0
  · intro hmean y
    apply (sphereHarmonicCoordinate_zero_eq_zero_iff hO hD _).mp
    have hz : sphereSobolevCoefficientL (5/2 : ℝ) 0 (U5 y) = 0 := by
      have h := (sphereHarmonicCoordinate_zero_eq_zero_iff hO hD _).mpr (hmean y)
      rw [sphereHarmonicCoordinate_zeroEquiv_symm_inclusion hO hD (5/2 : ℝ)
        (by norm_num)] at h
      exact h
    change sphereHarmonicCoordinate hO hD 0
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
          (sphereSobolevPartialSumL (3/2 : ℝ) n (u y)))) = 0
    rw [sphereHarmonicCoordinate_zeroEquiv_symm_inclusion hO hD (3/2 : ℝ)
      (by norm_num), sphereSobolevPartialSumL_apply,
      sphereSobolevCoefficientL_partialSum]
    by_cases hn : 0 < n
    · simp only [hn, if_true]
      rw [sphereSobolevCoefficientL_inclusion]
      exact hz
    · simp only [hn, if_false]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
