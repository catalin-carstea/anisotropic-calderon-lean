import Calderon.ActualSphereSobolevConstantOne
import Calderon.SphereSobolevAngularRaisingSingle
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MvPolynomial
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open HarmonicDerivativeOperator

private lemma single_index_heq (s t : ℝ) (hst : s=t) (k : ℕ) (v : harmonicSphereSubspace k) :
    HEq (sphereSobolevSingleL s k v) (sphereSobolevSingleL t k v) := by
  cases hst
  rfl

def constantOneDoubleRaisingHalf (hF : SphereFischerInner) (i j : Fin 3) : SphereSobolev (1/2:ℝ) :=
  sphereSobolevSingleL (1/2:ℝ) 2
    (harmonicDerivativeAdjoint hF 1 i (harmonicDerivativeAdjoint hF 0 j
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩))

theorem sphereSobolevInclusionL_constantOneDoubleRaisingHalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (constantOneDoubleRaisingHalf hF i j) =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) j
          (sphereSobolevConstantOne (3/2:ℝ))) := by
  let v0 : harmonicSphereSubspace 0 :=
    ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩
  let v1 := harmonicDerivativeAdjoint hF 0 j v0
  let v2 := harmonicDerivativeAdjoint hF 1 i v1
  have hHigh : sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) j
      (sphereSobolevConstantOne (3/2:ℝ)) = sphereSobolevSingleL (1/2:ℝ) 1 v1 := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2:ℝ) j 0 v0
    have hIndex : sphereSobolevSingleL ((3/2:ℝ)-1) 1 v1 = sphereSobolevSingleL (1/2:ℝ) 1 v1 :=
      eq_of_heq (single_index_heq _ _ (by norm_num) 1 v1)
    exact h.trans hIndex
  have hLow : sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i
      (sphereSobolevSingleL (1/2:ℝ) 1 v1) = sphereSobolevSingleL (-(1/2:ℝ)) 2 v2 := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2:ℝ) i 1 v1
    have hIndex : sphereSobolevSingleL ((1/2:ℝ)-1) 2 v2 = sphereSobolevSingleL (-(1/2:ℝ)) 2 v2 :=
      eq_of_heq (single_index_heq _ _ (by norm_num) 2 v2)
    exact h.trans hIndex
  have hI : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (constantOneDoubleRaisingHalf hF i j) = sphereSobolevSingleL (-(1/2:ℝ)) 2 v2 :=
    sphereSobolevInclusionL_single (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) 2 v2
  exact hI.trans ((congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i)
    hHigh).trans hLow).symm

theorem sphereSobolevInclusionL_sum_constantOneDoubleRaisingHalf
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a : Fin 3 → Fin 3 → ℝ) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (∑ i : Fin 3, ∑ j : Fin 3, a i j • constantOneDoubleRaisingHalf hF i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, a i j •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2:ℝ) i
          (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) j
            (sphereSobolevConstantOne (3/2:ℝ))) := by
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun v => a i j • v)
    (sphereSobolevInclusionL_constantOneDoubleRaisingHalf hF hO hD i j)

theorem exists_constantOneDoubleRaisingHalf_sum_norm_bound
    (hF : SphereFischerInner) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (a : Fin 3 → Fin 3 → ℝ) (C0 : ℝ), 0 ≤ C0 →
      (∀ i j, |a i j| ≤ C0) →
      ‖∑ i : Fin 3, ∑ j : Fin 3, a i j • constantOneDoubleRaisingHalf hF i j‖ ≤ M*C0 := by
  let S := ∑ i : Fin 3, ∑ j : Fin 3, ‖constantOneDoubleRaisingHalf hF i j‖
  have hS : 0 ≤ S := by positivity
  refine ⟨1+S,by linarith,?_⟩
  intro a C0 hC0 ha
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, a i j • constantOneDoubleRaisingHalf hF i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖a i j • constantOneDoubleRaisingHalf hF i j‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, |a i j| * ‖constantOneDoubleRaisingHalf hF i j‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, C0*‖constantOneDoubleRaisingHalf hF i j‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_right (ha i j) (norm_nonneg _)))
    _ = C0*S := by simp only [S,Finset.mul_sum]
    _ ≤ (1+S)*C0 := by linarith only [hC0]

end OAI.AnisotropicCalderon.SphereHarmonic
