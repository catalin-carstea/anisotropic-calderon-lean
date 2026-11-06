import Calderon.SphereSobolevMidpointExtension
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

theorem sphereInterpolation_subtype_pseudoEMetric_eq
    (V : Type*) [PseudoMetricSpace V] (S : Set V) :
    (inferInstance : PseudoMetricSpace S).toPseudoEMetricSpace =
      (inferInstance : PseudoEMetricSpace S) := by
  rfl

theorem sphereInterpolation_metric_pseudoEMetric_eq
    (V : Type*) [MetricSpace V] :
    (inferInstance : PseudoMetricSpace V).toPseudoEMetricSpace =
      (inferInstance : EMetricSpace V).toPseudoEMetricSpace := by
  rfl

theorem sphereInterpolation_subtype_clm_lipschitz
    {V W Z : Type*} [PseudoMetricSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (s : Set V) (f : s → (W →L[ℝ] Z))
    (h : ∀ x y, dist (f x) (f y) ≤ dist (x : V) (y : V)) :
    LipschitzWith 1 f := by
  apply LipschitzWith.mk_one
  intro x y
  exact h x y

theorem sphereInterpolation_clm_dist_eq_norm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T S : V →L[ℝ] W) : dist T S = ‖T-S‖ := dist_eq_norm T S

theorem sphereInterpolation_pair_clm_dist_eq_norm
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (T S : (A →L[ℝ] B) × (C →L[ℝ] D)) :
    dist T S = ‖T-S‖ := dist_eq_norm T S

theorem sphereSobolevEndpointCompatibility_add
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (J : C →L[ℝ] D) (K : A →L[ℝ] B)
    (T S : (B →L[ℝ] D) × (A →L[ℝ] C))
    (hT : J.comp T.2 = T.1.comp K) (hS : J.comp S.2 = S.1.comp K) :
    J.comp (T.2+S.2) = (T.1+S.1).comp K := by
  calc
    J.comp (T.2+S.2) = J.comp T.2+J.comp S.2 := J.comp_add T.2 S.2
    _ = T.1.comp K+S.1.comp K := congrArg₂ (fun X Y => X+Y) hT hS
    _ = (T.1+S.1).comp K := (T.1.add_comp S.1 K).symm

theorem sphereSobolevEndpointCompatibility_smul
    {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (J : C →L[ℝ] D) (K : A →L[ℝ] B)
    (T : (B →L[ℝ] D) × (A →L[ℝ] C)) (c : ℝ)
    (hT : J.comp T.2 = T.1.comp K) :
    J.comp (c • T.2) = (c • T.1).comp K := by
  calc
    J.comp (c • T.2) = c • J.comp T.2 := J.comp_smul c T.2
    _ = c • T.1.comp K := congrArg (fun X => c • X) hT
    _ = (c • T.1).comp K := (ContinuousLinearMap.smul_comp c T.1 K).symm

abbrev SphereSobolevEndpointPair :=
  (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ)) ×
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))

def sphereSobolevCompatibleEndpoints : Submodule ℝ SphereSobolevEndpointPair where
  carrier := {T | (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp T.2 =
    T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))}
  zero_mem' := by
    change (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp 0 =
      (0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ)).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    rw [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  add_mem' := by
    intro T S hT hS
    change (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp (T.2+S.2) =
      (T.1+S.1).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    exact sphereSobolevEndpointCompatibility_add _ _ T S hT hS
  smul_mem' := by
    intro c T hT
    change (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp (c • T.2) =
      (c • T.1).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    exact sphereSobolevEndpointCompatibility_smul _ _ T c hT

/-- The existing subtype module with its existing restricted maximum norm. -/
instance sphereSobolevCompatibleEndpointsNormedSpace :
    NormedSpace ℝ sphereSobolevCompatibleEndpoints where
  toModule := sphereSobolevCompatibleEndpoints.module
  norm_smul_le c T := by
    change max ‖c • T.1.1‖ ‖c • T.1.2‖ ≤ ‖c‖ * max ‖T.1.1‖ ‖T.1.2‖
    apply max_le
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.2).trans
        (mul_le_mul_of_nonneg_left (le_max_right ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))

theorem sphereSobolevCompatibleEndpointsNormedSpace_module_eq :
    sphereSobolevCompatibleEndpointsNormedSpace.toModule =
      sphereSobolevCompatibleEndpoints.module := by
  rfl

def sphereInterpolationBoundedLinearMap
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →ₗ[ℝ] Y) (C : ℝ) (hA : ∀ x, ‖A x‖ ≤ C*‖x‖) : X →L[ℝ] Y :=
  A.mkContinuous C hA

local instance sphereSobolevCompatibleMidpointOperatorNorm :
    Norm (sphereSobolevCompatibleEndpoints →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) := by
  have hNorm := ContinuousLinearMap.hasOpNorm
    (E := sphereSobolevCompatibleEndpoints)
    (F := SphereSobolev 1 →L[ℝ] SphereSobolev 0) (σ₁₂ := RingHom.id ℝ)
  simpa only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    sphereSobolevCompatibleEndpointsNormedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using hNorm

def sphereSobolevCompatibleMidpoint (T : sphereSobolevCompatibleEndpoints) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  sphereSobolevMidpointL T.1.1 T.1.2 T.2

theorem sphereSobolevCompatibleMidpoint_inclusion_apply
    (T : sphereSobolevCompatibleEndpoints) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
      (sphereSobolevCompatibleMidpoint T u) =
    T.1.1 (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u) := by
  exact congrArg (fun L : SphereSobolev 1 →L[ℝ] SphereSobolev (-1/2 : ℝ) => L u)
    (sphereSobolevInclusionL_midpoint T.1.1 T.1.2 T.2)

theorem norm_sphereSobolevCompatibleMidpoint_le
    (T : sphereSobolevCompatibleEndpoints) :
    ‖sphereSobolevCompatibleMidpoint T‖ ≤ ‖T‖ := by
  calc
    _ ≤ (‖T.1.1‖+‖T.1.2‖)/2 := norm_sphereSobolevMidpointL_le T.1.1 T.1.2 T.2
    _ ≤ ‖T‖ := by
      change (‖T.1.1‖+‖T.1.2‖)/2 ≤ max ‖T.1.1‖ ‖T.1.2‖
      linarith [le_max_left ‖T.1.1‖ ‖T.1.2‖,le_max_right ‖T.1.1‖ ‖T.1.2‖]

theorem sphereSobolevCompatibleMidpoint_add (T S : sphereSobolevCompatibleEndpoints) :
    sphereSobolevCompatibleMidpoint (T+S) =
      sphereSobolevCompatibleMidpoint T+sphereSobolevCompatibleMidpoint S := by
  apply ContinuousLinearMap.ext
  intro u
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
  let v : SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u
  have hT : J (sphereSobolevCompatibleMidpoint T u) = T.1.1 v :=
    sphereSobolevCompatibleMidpoint_inclusion_apply T u
  have hS : J (sphereSobolevCompatibleMidpoint S u) = S.1.1 v :=
    sphereSobolevCompatibleMidpoint_inclusion_apply S u
  have hTS : J (sphereSobolevCompatibleMidpoint (T+S) u) = T.1.1 v+S.1.1 v :=
    sphereSobolevCompatibleMidpoint_inclusion_apply (T+S) u
  have hadd : J (sphereSobolevCompatibleMidpoint T u+sphereSobolevCompatibleMidpoint S u) =
      T.1.1 v+S.1.1 v :=
    (J.map_add _ _).trans (congrArg₂
      (fun x y : SphereSobolev (-1/2 : ℝ) => x+y) hT hS)
  exact sphereSobolevInclusionL_injective 0 (-1/2 : ℝ) (by norm_num)
    (hTS.trans hadd.symm)

theorem sphereSobolevCompatibleMidpoint_smul (c : ℝ) (T : sphereSobolevCompatibleEndpoints) :
    sphereSobolevCompatibleMidpoint (c • T) = c • sphereSobolevCompatibleMidpoint T := by
  apply ContinuousLinearMap.ext
  intro u
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
  let v : SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u
  have hT : J (sphereSobolevCompatibleMidpoint T u) = T.1.1 v :=
    sphereSobolevCompatibleMidpoint_inclusion_apply T u
  have hcT : J (sphereSobolevCompatibleMidpoint (c • T) u) = c • T.1.1 v :=
    sphereSobolevCompatibleMidpoint_inclusion_apply (c • T) u
  have hsmul : J (c • sphereSobolevCompatibleMidpoint T u) = c • T.1.1 v :=
    (J.map_smul c _).trans (congrArg (fun x : SphereSobolev (-1/2 : ℝ) => c • x) hT)
  exact sphereSobolevInclusionL_injective 0 (-1/2 : ℝ) (by norm_num)
    (hcT.trans hsmul.symm)

def sphereSobolevCompatibleMidpointLinear :
    sphereSobolevCompatibleEndpoints →ₗ[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) where
  toFun := sphereSobolevCompatibleMidpoint
  map_add' := sphereSobolevCompatibleMidpoint_add
  map_smul' := sphereSobolevCompatibleMidpoint_smul

theorem dist_sphereSobolevCompatibleMidpoint_le
    (T S : sphereSobolevCompatibleEndpoints) :
    dist (sphereSobolevCompatibleMidpoint T) (sphereSobolevCompatibleMidpoint S) ≤
      dist (T : SphereSobolevEndpointPair) (S : SphereSobolevEndpointPair) := by
  have hsub : sphereSobolevCompatibleMidpoint (T-S) =
      sphereSobolevCompatibleMidpoint T-sphereSobolevCompatibleMidpoint S :=
    map_sub sphereSobolevCompatibleMidpointLinear T S
  calc
    dist (sphereSobolevCompatibleMidpoint T) (sphereSobolevCompatibleMidpoint S) =
        ‖sphereSobolevCompatibleMidpoint T-sphereSobolevCompatibleMidpoint S‖ :=
      sphereInterpolation_clm_dist_eq_norm _ _
    _ = ‖sphereSobolevCompatibleMidpoint (T-S)‖ := congrArg norm hsub.symm
    _ ≤ ‖T-S‖ := norm_sphereSobolevCompatibleMidpoint_le (T-S)
    _ = dist (T : SphereSobolevEndpointPair) (S : SphereSobolevEndpointPair) :=
      (sphereInterpolation_pair_clm_dist_eq_norm T.1 S.1).symm

theorem lipschitzWith_sphereSobolevCompatibleMidpoint :
    LipschitzWith 1 sphereSobolevCompatibleMidpoint := by
  exact sphereInterpolation_subtype_clm_lipschitz
    (V := SphereSobolevEndpointPair) (W := SphereSobolev 1) (Z := SphereSobolev 0)
    (sphereSobolevCompatibleEndpoints : Set SphereSobolevEndpointPair)
    sphereSobolevCompatibleMidpoint dist_sphereSobolevCompatibleMidpoint_le

def sphereSobolevCompatibleMidpointL :
    sphereSobolevCompatibleEndpoints →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) where
  toLinearMap := sphereSobolevCompatibleMidpointLinear
  cont := lipschitzWith_sphereSobolevCompatibleMidpoint.continuous

theorem sphereSobolevCompatibleMidpointL_apply (T : sphereSobolevCompatibleEndpoints) :
    sphereSobolevCompatibleMidpointL T = sphereSobolevMidpointL T.1.1 T.1.2 T.2 := rfl

theorem norm_sphereSobolevCompatibleMidpointL_le : ‖sphereSobolevCompatibleMidpointL‖ ≤ 1 := by
  have hBound := ContinuousLinearMap.opNorm_le_bound
    (E := sphereSobolevCompatibleEndpoints)
    (F := SphereSobolev 1 →L[ℝ] SphereSobolev 0) (σ₁₂ := RingHom.id ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    sphereSobolevCompatibleEndpointsNormedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hBound
  apply hBound sphereSobolevCompatibleMidpointL zero_le_one
  intro T
  change ‖sphereSobolevCompatibleMidpoint T‖ ≤ 1*‖T‖
  simpa only [one_mul] using norm_sphereSobolevCompatibleMidpoint_le T

theorem sphereSobolevCompatibleMidpointL_lower_inclusion (T : sphereSobolevCompatibleEndpoints) :
    (sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)).comp
      (sphereSobolevCompatibleMidpointL T) =
    T.1.1.comp (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)) :=
  sphereSobolevInclusionL_midpoint T.1.1 T.1.2 T.2

theorem sphereSobolevCompatibleMidpointL_upper_inclusion (T : sphereSobolevCompatibleEndpoints) :
    (sphereSobolevCompatibleMidpointL T).comp
      (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)) =
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).comp T.1.2 :=
  sphereSobolevMidpointL_inclusion T.1.1 T.1.2 T.2

end OAI.AnisotropicCalderon.SphereHarmonic
