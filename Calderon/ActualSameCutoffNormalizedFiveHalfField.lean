import Calderon.ActualSphereSobolevConstantOne
import Calderon.ActualSameFiveHalfSourceCoreApprox

set_option autoImplicit false
noncomputable section
open Set Metric MvPolynomial Filter Function
open scoped ENNReal ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  PositiveSpectralCore ConformalDepth
open OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The high angular class for the original cutoff density after subtracting
its literal degree-zero constant sphere function. -/
def normalizedFiveHalfSourceField (chi : R3 → ℝ)
    (Psi5 : R3 → SphereSobolev (5/2 : ℝ)) :
    R3 → SphereSobolev (5/2 : ℝ) :=
  fun y => chi y • (Psi5 y - sphereSobolevConstantOne (5/2 : ℝ))

def normalizedThreeHalfSourceField (chi : R3 → ℝ)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) :
    R3 → SphereSobolev (3/2 : ℝ) :=
  fun y => chi y • (Psi y - sphereSobolevConstantOne (3/2 : ℝ))

/-- The SAME selected cutoff and original low field determine the normalized
high field, whose fixed-frame fiber mean is zero everywhere. -/
theorem normalizedFiveHalfSourceField_properties
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
          polynomialSphereL2 (C 1))) = 0) :
    let V5 := normalizedFiveHalfSourceField chi Psi5
    let v3 := normalizedThreeHalfSourceField chi Psi
    ContDiff ℝ ∞ V5 ∧ HasCompactSupport V5 ∧
    (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (V5 y)) = v3 ∧
    tsupport V5 ⊆ tsupport chi ∧
    (∀ y : R3, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (5/2 : ℝ) 0 (by norm_num) (V5 y))) = 0) := by
  dsimp only
  let V5 := normalizedFiveHalfSourceField chi Psi5
  let v3 := normalizedThreeHalfSourceField chi Psi
  have hV5 : ContDiff ℝ ∞ V5 := by
    change ContDiff ℝ ∞ (fun y => chi y • (Psi5 y - sphereSobolevConstantOne (5/2 : ℝ)))
    exact hchi.smul (hPsi5.sub contDiff_const)
  have hV5Comp : HasCompactSupport V5 := by
    change HasCompactSupport (chi • (fun y => Psi5 y - sphereSobolevConstantOne (5/2 : ℝ)))
    exact hchiComp.smul_right
  have hLow : (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ)
      (by norm_num) (V5 y)) = v3 := by
    funext y
    by_cases hc : chi y = 0
    · simp [V5,v3,normalizedFiveHalfSourceField,normalizedThreeHalfSourceField,hc]
    · have hy : y ∈ cylinder := by
        exact interior_subset (hchiSupp (subset_tsupport chi hc))
      simp only [V5,v3,normalizedFiveHalfSourceField,normalizedThreeHalfSourceField,
        map_smul,map_sub,hInc y hy,
        sphereSobolevInclusionL_constantOne (5/2 : ℝ) (3/2 : ℝ) (by norm_num)]
  have hSupp : tsupport V5 ⊆ tsupport chi := by
    apply closure_mono
    intro y hy
    change V5 y ≠ 0 at hy
    change chi y ≠ 0
    intro hc
    simp [V5,normalizedFiveHalfSourceField,hc] at hy
  have hH0 (y : R3) :
      (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (5/2 : ℝ) 0 (by norm_num) (V5 y)) =
      chi y • ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) -
        polynomialSphereL2 (C 1)) := by
    have htrans := congrArg (fun T : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev 0 =>
      T (V5 y))
      (sphereSobolevInclusionL_trans (5/2 : ℝ) (3/2 : ℝ) 0
        (by norm_num) (by norm_num))
    have h1 : sphereSobolevInclusionL (5/2 : ℝ) 0 (by norm_num) (V5 y) =
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (v3 y) := by
      calc
        sphereSobolevInclusionL (5/2 : ℝ) 0 (by norm_num) (V5 y) =
            sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
              (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (V5 y)) := by
          simpa only [ContinuousLinearMap.comp_apply] using htrans.symm
        _ = sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (v3 y) := by
          rw [congrFun hLow y]
    rw [h1]
    simp only [v3,normalizedThreeHalfSourceField,map_smul,map_sub,
      sphereSobolevInclusionL_constantOne (3/2 : ℝ) 0 (by norm_num),
      sphereSobolevZeroEquiv_symm_constantOne]
  exact ⟨hV5,hV5Comp,hLow,hSupp,fun y => by rw [hH0 y]; exact hMean0 y⟩

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
