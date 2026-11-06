import Calderon.ActualFiniteCoreSobolevLift
import Calderon.SphereSobolevPartialSumOperator

/-! The original compact smooth cutoff, with no moving-output image assumption. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevPartialSumL
  finiteCoreSobolevLift

lemma sphereHarmonicCoordinate_zeroEquiv_symm_inclusion
    (s : ℝ) (hs : 0 ≤ s) (v : SphereSobolev s) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k
      ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL s 0 hs v)) =
      sphereSobolevCoefficientL s k v := by
  let Z := sphereSobolevZeroEquiv hO hD
  calc
    _ = sphereSobolevCoefficientL 0 k
        (Z (Z.symm (sphereSobolevInclusionL s 0 hs v))) :=
      (sphereSobolevCoefficientL_zeroEquiv hO hD k
        (Z.symm (sphereSobolevInclusionL s 0 hs v))).symm
    _ = sphereSobolevCoefficientL 0 k (sphereSobolevInclusionL s 0 hs v) :=
      congrArg (sphereSobolevCoefficientL 0 k) (Z.apply_symm_apply _)
    _ = _ := sphereSobolevCoefficientL_inclusion s 0 hs v k

def finitePartialSumCore (n : ℕ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    smoothCompactFiniteSphereCore hO hD := by
  let C : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereL2 :=
    (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)).comp
        (sphereSobolevPartialSumL (3/2 : ℝ) n))
  refine ⟨fun x => C (u x), C.contDiff.comp hu, hc.comp_left C.map_zero, n, ?_⟩
  intro x k hk
  change sphereHarmonicCoordinate hO hD k
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (sphereSobolevPartialSumL (3/2 : ℝ) n (u x)))) = 0
  rw [sphereHarmonicCoordinate_zeroEquiv_symm_inclusion,
    sphereSobolevPartialSumL_apply, sphereSobolevCoefficientL_partialSum,
    if_neg (not_lt.mpr hk)]

lemma finiteCoreSobolevLift_finitePartialSumCore
    (n : ℕ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (x : R3) :
    finiteCoreSobolevLift hO hD (3/2 : ℝ) (finitePartialSumCore hO hD n u hu hc) x =
      sphereSobolevPartialSumL (3/2 : ℝ) n (u x) := by
  apply sphereSobolev_ext (3/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift]
  change sphereHarmonicCoordinate hO hD k
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (sphereSobolevPartialSumL (3/2 : ℝ) n (u x)))) = _
  exact sphereHarmonicCoordinate_zeroEquiv_symm_inclusion hO hD (3/2 : ℝ)
    (by norm_num) (sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) k

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.sphereHarmonicCoordinate_zeroEquiv_symm_inclusion
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.finitePartialSumCore
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.finiteCoreSobolevLift_finitePartialSumCore
