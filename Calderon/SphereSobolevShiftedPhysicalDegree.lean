import Calderon.SharpRadialCoefficientOperators
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph
/-! Original physical degree k, actual order loss one, degree zero retained. -/

def sphereSobolevShiftedDegreeL (s : ℝ) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  (sphereSobolevBesselEquiv s 1).toContinuousLinearEquiv.toContinuousLinearMap -
    sphereSobolevInclusionL s (s-1) (by linarith)

lemma sphereSobolevCoefficientL_shiftedDegree (s : ℝ) (k : ℕ) (u : SphereSobolev s) :
    sphereSobolevCoefficientL (s-1) k (sphereSobolevShiftedDegreeL s u) =
      (k:ℝ) • sphereSobolevCoefficientL s k u := by
  have hB := sphereSobolevCoefficientL_besselEquiv s 1 k u
  have hI := sphereSobolevCoefficientL_inclusion s (s-1) (by linarith) u k
  have hValue : sphereSobolevShiftedDegreeL s u = sphereSobolevBesselEquiv s 1 u -
      sphereSobolevInclusionL s (s-1) (by linarith) u := rfl
  calc
    _ = sphereSobolevCoefficientL (s-1) k (sphereSobolevBesselEquiv s 1 u) -
        sphereSobolevCoefficientL (s-1) k (sphereSobolevInclusionL s (s-1) (by linarith) u) :=
      (congrArg (sphereSobolevCoefficientL (s-1) k) hValue).trans
        ((sphereSobolevCoefficientL (s-1) k).map_sub _ _)
    _ = besselWeight 1 k • sphereSobolevCoefficientL s k u - sphereSobolevCoefficientL s k u :=
      congrArg₂ (fun x y : harmonicSphereSubspace k => x-y) hB hI
    _ = _ := by
      simp only [besselWeight,Real.rpow_one]
      exact sphereCoefficient_one_add_smul_sub (k:ℝ) (sphereSobolevCoefficientL s k u)

lemma sphereSobolevShiftedDegreeL_single (s : ℝ) (k : ℕ) (z : harmonicSphereSubspace k) :
    sphereSobolevShiftedDegreeL s (sphereSobolevSingleL s k z) =
      (k:ℝ) • sphereSobolevSingleL (s-1) k z := by
  apply sphereSobolev_ext (s-1)
  intro m
  have hRight := (sphereSobolevCoefficientL (s-1) m).map_smul (k:ℝ) (sphereSobolevSingleL (s-1) k z)
  have hLeft := sphereSobolevCoefficientL_shiftedDegree s m (sphereSobolevSingleL s k z)
  by_cases hm : m=k
  · subst m
    exact hLeft.trans ((congrArg (fun x : harmonicSphereSubspace k => (k:ℝ) • x)
      ((sphereSobolevCoefficientL_single_self s k z).trans
        (sphereSobolevCoefficientL_single_self (s-1) k z).symm)).trans hRight.symm)
  · have hzL := sphereSobolevCoefficientL_single_ne s k m hm z
    have hzR := sphereSobolevCoefficientL_single_ne (s-1) k m hm z
    rw [hzL,smul_zero] at hLeft
    rw [hzR,smul_zero] at hRight
    exact hLeft.trans hRight.symm

lemma sphereSobolevShiftedDegreeL_one_eq_degree : sphereSobolevShiftedDegreeL 1 = sphereSobolevDegreeL := by
  apply ContinuousLinearMap.ext
  intro u
  have hInclusion : sphereSobolevInclusionL 1 ((1:ℝ)-1) (by linarith) u =
      sphereSobolevInclusionL 1 0 (by norm_num) u := by
    apply sphereSobolev_ext 0
    intro k
    have hOrder : sphereSobolevCoefficientL 0 k (sphereSobolevInclusionL 1 ((1:ℝ)-1) (by linarith) u) =
        sphereSobolevCoefficientL ((1:ℝ)-1) k (sphereSobolevInclusionL 1 ((1:ℝ)-1) (by linarith) u) :=
      congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
        (sphereSobolevInclusionL 1 ((1:ℝ)-1) (by linarith) u)) (sub_self (1:ℝ)).symm
    exact hOrder.trans ((sphereSobolevCoefficientL_inclusion 1 ((1:ℝ)-1) (by linarith) u k).trans
      (sphereSobolevCoefficientL_inclusion 1 0 (by norm_num) u k).symm)
  change sphereSobolevBesselEquiv 1 1 u - sphereSobolevInclusionL 1 ((1:ℝ)-1) (by linarith) u =
    sphereSobolevBesselEquiv 1 1 u - sphereSobolevInclusionL 1 0 (by norm_num) u
  exact congrArg (fun z : SphereSobolev 0 => sphereSobolevBesselEquiv 1 1 u-z) hInclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevShiftedDegreeL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_shiftedDegree
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevShiftedDegreeL_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevShiftedDegreeL_one_eq_degree
end OAI.AnisotropicCalderon.SphereHarmonic
