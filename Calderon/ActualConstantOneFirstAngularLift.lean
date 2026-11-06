import Calderon.ActualConstantOneDoubleRaisingHalfLift
import Calderon.ActualNativeLeadingAngularCancellation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MvPolynomial
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open HarmonicDerivativeOperator

private lemma single_index_heq (s t : ℝ) (hst : s=t) (k : ℕ) (v : harmonicSphereSubspace k) :
    HEq (sphereSobolevSingleL s k v) (sphereSobolevSingleL t k v) := by cases hst; rfl

def constantOneFirstRaisingThreeHalf (hF : SphereFischerInner) (j : Fin 3) : SphereSobolev (3/2:ℝ) :=
  sphereSobolevSingleL (3/2:ℝ) 1 (harmonicDerivativeAdjoint hF 0 j
    ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩)

theorem sphereSobolevAngularCoordinateTransposeL_constantOne_fivehalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (j : Fin 3) :
    sphereSobolevAngularCoordinateTransposeL hF hO hD (5/2:ℝ) j (sphereSobolevConstantOne (5/2:ℝ)) =
      constantOneFirstRaisingThreeHalf hF j := by
  let v0 : harmonicSphereSubspace 0 :=
    ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (5/2:ℝ) j 0 v0
  exact h.trans (eq_of_heq (single_index_heq _ _ (by norm_num) 1 (harmonicDerivativeAdjoint hF 0 j v0)))

theorem sphereSobolevInclusionL_constantOneFirstRaisingThreeHalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (j : Fin 3) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (constantOneFirstRaisingThreeHalf hF j) =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) j (sphereSobolevConstantOne (3/2:ℝ)) := by
  let v0 : harmonicSphereSubspace 0 :=
    ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩
  let v1 := harmonicDerivativeAdjoint hF 0 j v0
  have hI : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (constantOneFirstRaisingThreeHalf hF j) = sphereSobolevSingleL (1/2:ℝ) 1 v1 :=
    sphereSobolevInclusionL_single (3/2:ℝ) (1/2:ℝ) (by norm_num) 1 v1
  have hA := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2:ℝ) j 0 v0
  have hIndex : sphereSobolevSingleL ((3/2:ℝ)-1) 1 v1 = sphereSobolevSingleL (1/2:ℝ) 1 v1 :=
    eq_of_heq (single_index_heq _ _ (by norm_num) 1 v1)
  exact hI.trans (hA.trans hIndex).symm

theorem sphereSobolevShiftedDegreeL_constantOneFirstRaisingThreeHalf
    (hF : SphereFischerInner) (j : Fin 3) :
    sphereSobolevShiftedDegreeL (3/2:ℝ) (constantOneFirstRaisingThreeHalf hF j) =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (constantOneFirstRaisingThreeHalf hF j) := by
  unfold constantOneFirstRaisingThreeHalf
  rw [sphereSobolevShiftedDegreeL_single,sphereSobolevInclusionL_single]
  simp only [Nat.cast_one,one_smul]
  exact eq_of_heq (single_index_heq _ _ (by norm_num) 1 _)

theorem sphereSobolevAngularCoordinateTransposeL_constantOneFirstRaisingThreeHalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) :
    sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) i (constantOneFirstRaisingThreeHalf hF j) =
      constantOneDoubleRaisingHalf hF i j := by
  unfold constantOneFirstRaisingThreeHalf
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2:ℝ) i 1
    (harmonicDerivativeAdjoint hF 0 j
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩)
  exact h.trans (eq_of_heq (single_index_heq _ _ (by norm_num) 2 _))

theorem sum_constantOneDoubleRaisingHalf_diagonal_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    (∑ i : Fin 3, constantOneDoubleRaisingHalf hF i i) = 0 := by
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  rw [map_sum,map_zero]
  have hTerms (i : Fin 3) := sphereSobolevInclusionL_constantOneDoubleRaisingHalf hF hO hD i i
  calc
    _ = ∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) i (sphereSobolevConstantOne (3/2:ℝ))) :=
      Finset.sum_congr rfl (fun i _ => hTerms i)
    _ = 0 := OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_sphereSobolevAngularCoordinateTranspose_twice_eq_zero
      hF hO hD (sphereSobolevConstantOne (3/2:ℝ))

end OAI.AnisotropicCalderon.SphereHarmonic
