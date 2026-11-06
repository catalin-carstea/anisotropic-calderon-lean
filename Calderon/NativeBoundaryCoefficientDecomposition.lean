import Calderon.NativeCoefficientFluxTrace
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace Classical Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

def boundaryNormalCoefficientData (F : SmoothCoefficientMatrix 2) : SmoothData :=
  ⟨fun x : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
    x i*(coefficientSmoothData (F i j)).1 x*x j,
      ContDiff.sum fun i hi => ContDiff.sum fun j hj =>
        ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.mul
          (coefficientSmoothData (F i j)).2).mul (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff⟩

def boundaryTangentCoefficientData (F : SmoothCoefficientMatrix 2) (j : Fin 3) : SmoothData :=
  ⟨fun x : R3 => (∑ i : Fin 3, x i*(coefficientSmoothData (F i j)).1 x) -
    (boundaryNormalCoefficientData F).1 x*x j,
      (ContDiff.sum fun i hi => (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.mul
        (coefficientSmoothData (F i j)).2).sub
          ((boundaryNormalCoefficientData F).2.mul (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff)⟩

lemma sum_boundary_normal_coefficients (F : SmoothCoefficientMatrix 2) (x : R3) :
    (∑ j : Fin 3, (∑ i : Fin 3, x i*(coefficientSmoothData (F i j)).1 x)*x j) =
      (boundaryNormalCoefficientData F).1 x := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

lemma sum_boundaryTangentCoefficient_mul_coordinate_eq_zero
    (F : SmoothCoefficientMatrix 2) (x : UnitSphere) :
    (∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*x.val j) = 0 := by
  change (∑ j : Fin 3,
    ((∑ i : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val) -
      (boundaryNormalCoefficientData F).1 x.val*x.val j)*x.val j) = 0
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [sum_boundary_normal_coefficients]
  have he : (∑ j : Fin 3, (boundaryNormalCoefficientData F).1 x.val*x.val j*x.val j) =
      (boundaryNormalCoefficientData F).1 x.val := by
    calc
      _ = ∑ j : Fin 3, (boundaryNormalCoefficientData F).1 x.val*(x.val j)^2 :=
        Finset.sum_congr rfl (fun j hj => by ring)
      _ = (boundaryNormalCoefficientData F).1 x.val*(∑ j : Fin 3, (x.val j)^2) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [unitSphere_sum_sq,mul_one]
  rw [he,sub_self]

lemma boundary_coefficient_conormal_decomposition
    (F : SmoothCoefficientMatrix 2) (x : UnitSphere) (ξ : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val*ξ j) =
      (boundaryNormalCoefficientData F).1 x.val*⟪x.val,ξ⟫_ℝ +
        ∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*
          (ξ j-x.val j*⟪x.val,ξ⟫_ℝ) := by
  let n (j : Fin 3) : ℝ := ∑ i : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val
  have hn : (∑ i : Fin 3, ∑ j : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val*ξ j) =
      ∑ j : Fin 3, n j*ξ j := by
    rw [Finset.sum_comm]
    simp only [n,Finset.sum_mul]
  have he (j : Fin 3) : n j =
      (boundaryTangentCoefficientData F j).1 x.val+(boundaryNormalCoefficientData F).1 x.val*x.val j := by
    change n j = (n j-(boundaryNormalCoefficientData F).1 x.val*x.val j)+
      (boundaryNormalCoefficientData F).1 x.val*x.val j
    ring
  have hi : (∑ j : Fin 3, x.val j*ξ j) = ⟪x.val,ξ⟫_ℝ := sum_coordinate_mul_eq_inner _ _
  have ht : (∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*
      (ξ j-x.val j*⟪x.val,ξ⟫_ℝ)) =
        ∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*ξ j := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hm : (∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*
        (x.val j*⟪x.val,ξ⟫_ℝ)) = 0 := by
      simp only [← mul_assoc]
      rw [← Finset.sum_mul,sum_boundaryTangentCoefficient_mul_coordinate_eq_zero,zero_mul]
    rw [hm,sub_zero]
  rw [hn,ht]
  simp_rw [he,add_mul]
  rw [Finset.sum_add_distrib]
  have ha : (∑ j : Fin 3, ((boundaryNormalCoefficientData F).1 x.val*x.val j)*ξ j) =
      (boundaryNormalCoefficientData F).1 x.val*⟪x.val,ξ⟫_ℝ := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum,hi]
  rw [ha,add_comm]

lemma boundaryNormalCoefficientData_lower_bound
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (x : UnitSphere) : lam ≤ (boundaryNormalCoefficientData F).1 x.val := by
  let ξ : R3 := x.val
  have hc : Continuous (fun z : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
      ξ i*(coefficientSmoothData (F i j)).1 z*ξ j) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    exact (continuous_const.mul (coefficientSmoothData (F i j)).2.continuous).mul continuous_const
  have hclosed : IsClosed {z : R3 | lam*‖ξ‖^2 ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ξ i*(coefficientSmoothData (F i j)).1 z*ξ j} :=
    isClosed_le continuous_const hc
  have hball : (ballOpens : Set R3) ⊆ {z : R3 | lam*‖ξ‖^2 ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ξ i*(coefficientSmoothData (F i j)).1 z*ξ j} := by
    intro z hz
    have h := hUE.lower_bound hz ξ
    simpa only [Set.mem_setOf_eq,Matrix.toQuadraticForm'_apply,Matrix.mulVec,dotProduct,
      Finset.mul_sum,coefficientMatrixField,coefficientSmoothData,mul_assoc] using h
  have hx : x.val ∈ closure (ballOpens : Set R3) := by
    change x.val ∈ closure (Metric.ball (0 : R3) 1)
    rw [closure_ball (0 : R3) (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall x.property
  have h := (closure_minimal hball hclosed) hx
  have hnorm : ‖ξ‖ = 1 := by
    exact norm_eq_of_mem_sphere x
  change lam*‖ξ‖^2 ≤ (boundaryNormalCoefficientData F).1 x.val at h
  simpa only [hnorm,one_pow,mul_one] using h

lemma boundaryNormalCoefficientData_pos
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (x : UnitSphere) : 0 < (boundaryNormalCoefficientData F).1 x.val :=
  hUE.pos.trans_le (boundaryNormalCoefficientData_lower_bound F lam Lam hUE x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryNormalCoefficientData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryTangentCoefficientData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_boundary_normal_coefficients
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_boundaryTangentCoefficient_mul_coordinate_eq_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundary_coefficient_conormal_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryNormalCoefficientData_lower_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryNormalCoefficientData_pos
