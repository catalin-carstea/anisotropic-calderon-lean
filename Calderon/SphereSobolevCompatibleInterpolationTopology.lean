import Calderon.SphereSobolevCompatibleEndpointInterpolation
import Calderon.SmoothKernelCodomainRestriction
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

def sphereInterpolationEndpointDefectL
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (J : C →L[ℝ] D) (K : A →L[ℝ] B) :
    ((B →L[ℝ] D) × (A →L[ℝ] C)) →L[ℝ] (A →L[ℝ] D) :=
  ((ContinuousLinearMap.compL ℝ A C D J).comp (ContinuousLinearMap.snd ℝ _ _)) -
    (((ContinuousLinearMap.compL ℝ A B D).flip K).comp (ContinuousLinearMap.fst ℝ _ _))

def sphereSobolevEndpointDefectL : SphereSobolevEndpointPair →L[ℝ]
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ)) :=
  sphereInterpolationEndpointDefectL
    (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num))
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))

theorem sphereSobolevEndpointDefectL_eq_zero_iff (T : SphereSobolevEndpointPair) :
    sphereSobolevEndpointDefectL T = 0 ↔ T ∈ sphereSobolevCompatibleEndpoints := by
  change
    (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp T.2 -
        T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) = 0 ↔
      (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp T.2 =
        T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
  exact sub_eq_zero

instance sphereSobolevEndpointKernelNormedSpace :
    NormedSpace ℝ sphereSobolevEndpointDefectL.ker where
  toModule := sphereSobolevEndpointDefectL.ker.module
  norm_smul_le c T := by
    change max ‖c • T.1.1‖ ‖c • T.1.2‖ ≤ ‖c‖ * max ‖T.1.1‖ ‖T.1.2‖
    apply max_le
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.2).trans
        (mul_le_mul_of_nonneg_left (le_max_right ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))

theorem sphereSobolevEndpointKernelNormedSpace_module_eq :
    sphereSobolevEndpointKernelNormedSpace.toModule =
      sphereSobolevEndpointDefectL.ker.module := rfl

def sphereSobolevCompatibleEndpointsOfKernelL :
    sphereSobolevEndpointDefectL.ker →L[ℝ] sphereSobolevCompatibleEndpoints where
  toFun := fun T => ⟨T.1,(sphereSobolevEndpointDefectL_eq_zero_iff T.1).mp T.2⟩
  map_add' := fun T S => Subtype.ext rfl
  map_smul' := fun c T => Subtype.ext rfl
  cont := continuous_subtype_val.subtype_mk
    (fun T => (sphereSobolevEndpointDefectL_eq_zero_iff T.1).mp T.2)

theorem contDiff_sphereSobolevCompatibleEndpointsOfKernelL :
    ContDiff ℝ ∞ (sphereSobolevCompatibleEndpointsOfKernelL :
      sphereSobolevEndpointDefectL.ker → sphereSobolevCompatibleEndpoints) := by
  have hg := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := sphereSobolevEndpointDefectL.ker) (F := sphereSobolevCompatibleEndpoints) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    sphereSobolevEndpointKernelNormedSpace_module_eq,
    sphereSobolevCompatibleEndpointsNormedSpace_module_eq] at hg
  exact hg sphereSobolevCompatibleEndpointsOfKernelL

theorem contDiff_sphereSobolevCompatibleMidpointL :
    ContDiff ℝ ∞ (sphereSobolevCompatibleMidpointL :
      sphereSobolevCompatibleEndpoints → (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) := by
  have hg := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := sphereSobolevCompatibleEndpoints) (F := SphereSobolev 1 →L[ℝ] SphereSobolev 0) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    sphereSobolevEndpointKernelNormedSpace_module_eq,
    sphereSobolevCompatibleEndpointsNormedSpace_module_eq] at hg
  exact hg sphereSobolevCompatibleMidpointL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereSobolevEndpointKernelRestriction
    (T : E → SphereSobolevEndpointPair) (s : Set E)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints) :
    E → sphereSobolevEndpointDefectL.ker := by
  classical
  exact fun x => if hx : x ∈ s then
    ⟨T x,(sphereSobolevEndpointDefectL_eq_zero_iff (T x)).mpr (hT x hx)⟩ else 0

theorem contDiffOn_sphereSobolevEndpointKernelRestriction
    (T : E → SphereSobolevEndpointPair) (s : Set E) (hs : IsOpen s)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints)
    (hSmooth : ContDiffOn ℝ ∞ T s) :
    ContDiffOn ℝ ∞ (sphereSobolevEndpointKernelRestriction T s hT) s := by
  have hg := contDiffOn_kernelCodomainRestriction (E := E)
    (F := SphereSobolevEndpointPair)
    (G := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    sphereSobolevEndpointKernelNormedSpace_module_eq] at hg
  exact hg sphereSobolevEndpointDefectL T s hs.uniqueDiffOn hSmooth
    (fun x hx => (sphereSobolevEndpointDefectL_eq_zero_iff (T x)).mpr (hT x hx))

def sphereSobolevCompatibleInterpolationFamily
    (T : E → SphereSobolevEndpointPair) (s : Set E)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints) :
    E → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  fun x => sphereSobolevCompatibleMidpointL
    (sphereSobolevCompatibleEndpointsOfKernelL (sphereSobolevEndpointKernelRestriction T s hT x))

theorem sphereSobolevCompatibleInterpolationFamily_of_mem
    (T : E → SphereSobolevEndpointPair) (s : Set E)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints) (x : E) (hx : x ∈ s) :
    sphereSobolevCompatibleInterpolationFamily T s hT x =
      sphereSobolevMidpointL (T x).1 (T x).2 (hT x hx) := by
  simp only [sphereSobolevCompatibleInterpolationFamily,Function.comp_apply,
    sphereSobolevEndpointKernelRestriction,dif_pos hx]
  rfl

theorem contDiffOn_sphereSobolevCompatibleInterpolationFamily
    (T : E → SphereSobolevEndpointPair) (s : Set E) (hs : IsOpen s)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints)
    (hSmooth : ContDiffOn ℝ ∞ T s) :
    ContDiffOn ℝ ∞ (sphereSobolevCompatibleInterpolationFamily T s hT) s := by
  have hk := contDiffOn_sphereSobolevEndpointKernelRestriction T s hs hT hSmooth
  exact contDiff_sphereSobolevCompatibleMidpointL.comp_contDiffOn
    (contDiff_sphereSobolevCompatibleEndpointsOfKernelL.comp_contDiffOn hk)

theorem contDiffOn_of_eq_compatibleInterpolation
    (T : E → SphereSobolevEndpointPair) (s : Set E) (hs : IsOpen s)
    (hT : ∀ x ∈ s, T x ∈ sphereSobolevCompatibleEndpoints)
    (hSmooth : ContDiffOn ℝ ∞ T s)
    (M : E → (SphereSobolev 1 →L[ℝ] SphereSobolev 0))
    (hM : ∀ x (hx : x ∈ s), M x = sphereSobolevMidpointL (T x).1 (T x).2 (hT x hx)) :
    ContDiffOn ℝ ∞ M s := by
  apply (contDiffOn_sphereSobolevCompatibleInterpolationFamily T s hs hT hSmooth).congr
  intro x hx
  exact (hM x hx).trans (sphereSobolevCompatibleInterpolationFamily_of_mem T s hT x hx).symm

end OAI.AnisotropicCalderon.SphereHarmonic
