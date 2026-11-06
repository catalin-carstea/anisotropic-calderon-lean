import Calderon.ActualSameCutoffNormalizedFiveHalfField

set_option autoImplicit false
noncomputable section
open Set Metric MvPolynomial Filter Function
open scoped ENNReal ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  PositiveSpectralCore ConformalDepth
open OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- Literal mean-zero finite angular cores for the SAME cutoff density after
subtracting the actual degree-zero sphere function. -/
theorem exists_meanZero_finiteCore_normalized_fiveHalf_source
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiComp : HasCompactSupport chi) (hchiSupp : tsupport chi ⊆ interior cylinder)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (Psi5 : R3 → SphereSobolev (5/2 : ℝ)) (hPsi5 : ContDiff ℝ ∞ Psi5)
    (hInc : ∀ y ∈ cylinder,
      sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y)
    (hMean0 : ∀ y : R3, sphereMean (chi y •
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) -
          polynomialSphereL2 (C 1))) = 0) (n : ℕ) :
    ∃ F : smoothCompactFiniteSphereCore hO hD,
      (∀ y : R3, finiteCoreSobolevLift hO hD (3/2 : ℝ) F y =
        sphereSobolevPartialSumL (3/2 : ℝ) n
          (normalizedThreeHalfSourceField chi Psi y)) ∧
      tsupport (F : R3 → SphereL2) ⊆ tsupport chi ∧
      ∀ y : R3, sphereMean ((F : R3 → SphereL2) y) = 0 := by
  let V5 := normalizedFiveHalfSourceField chi Psi5
  let v3 := normalizedThreeHalfSourceField chi Psi
  obtain ⟨hV5,hComp,hLow,hSupp,hMeanV5⟩ :=
    normalizedFiveHalfSourceField_properties hO hD chi hchi hchiComp hchiSupp
      Psi Psi5 hPsi5 hInc hMean0
  obtain ⟨F,hLift,hFSupp,hFMean⟩ :=
    finiteCoreSobolevLift_sameFiveHalfPartialSum hO hD V5 hV5 hComp n
  refine ⟨F,?_,hFSupp.trans hSupp,hFMean hMeanV5⟩
  intro y
  calc
    finiteCoreSobolevLift hO hD (3/2 : ℝ) F y =
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
          (sphereSobolevPartialSumL (5/2 : ℝ) n (V5 y)) := hLift y
    _ = sphereSobolevPartialSumL (3/2 : ℝ) n
          (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (V5 y)) :=
      sphereSobolevInclusionL_sphereSobolevPartialSumL_fiveHalf n (V5 y)
    _ = sphereSobolevPartialSumL (3/2 : ℝ) n (v3 y) := by
      rw [congrFun hLow y]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
