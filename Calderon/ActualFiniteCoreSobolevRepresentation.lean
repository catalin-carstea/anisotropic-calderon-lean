import Calderon.ActualFiniteCoreSobolevLift
import Calderon.SphereSobolevPartialSumOperator

/-! Full AUTHOR upfront048, actual-Y-second-action-domain-author-oct16-v001.
Original finite-core INPUT representation, not an output image theorem. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity

lemma finiteCoreSobolevLift_representation
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : 0 ≤ s) (F : smoothCompactFiniteSphereCore hO hD) :
    let u : R3 → SphereSobolev s := finiteCoreSobolevLift hO hD s F
    ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ tsupport F.val ∧
      (∀ y : R3, sphereSobolevInclusionL s 0 hs (u y) = sphereSobolevZeroEquiv hO hD (F.val y)) ∧
      ∃ n : ℕ, (fun y => sphereSobolevPartialSumL s n (u y)) = u := by
  let u : R3 → SphereSobolev s := finiteCoreSobolevLift hO hD s F
  have hSupport : tsupport u ⊆ tsupport F.val := by
    apply closure_minimal ?_ (isClosed_tsupport F.val)
    intro y hy
    by_contra hOutside
    have hFZero : F.val y = 0 := image_eq_zero_of_notMem_tsupport hOutside
    apply hy
    apply sphereSobolev_ext s
    intro k
    calc
      sphereSobolevCoefficientL s k (u y) = sphereHarmonicCoordinate hO hD k (F.val y) :=
        sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD s F y k
      _ = 0 := (congrArg (sphereHarmonicCoordinate hO hD k) hFZero).trans
        (map_zero (sphereHarmonicCoordinate hO hD k))
      _ = sphereSobolevCoefficientL s k 0 := (map_zero (sphereSobolevCoefficientL s k)).symm
  have hCompact : HasCompactSupport u :=
    F.property.2.1.of_isClosed_subset (isClosed_tsupport u) hSupport
  have hValue (y : R3) :
      sphereSobolevInclusionL s 0 hs (u y) = sphereSobolevZeroEquiv hO hD (F.val y) := by
    apply sphereSobolev_ext 0
    intro k
    rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_finiteCoreSobolevLift,
      sphereSobolevCoefficientL_zeroEquiv]
  obtain ⟨n,hBand⟩ := F.property.2.2
  have hCut (y : R3) : sphereSobolevPartialSumL s n (u y) = u y := by
    apply sphereSobolev_ext s
    intro k
    rw [sphereSobolevPartialSumL_apply,sphereSobolevCoefficientL_partialSum]
    by_cases hk : k < n
    · simp only [if_pos hk]
    · have hZero : sphereSobolevCoefficientL s k (u y) = 0 :=
        (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD s F y k).trans
          (hBand y k (not_lt.mp hk))
      simp only [if_neg hk,hZero]
  exact ⟨contDiff_finiteCoreSobolevLift hO hD s F,hCompact,hSupport,hValue,n,funext hCut⟩

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.finiteCoreSobolevLift_representation
