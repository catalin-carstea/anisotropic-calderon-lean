import Calderon.ConformalFluxDivergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.Comp
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError

theorem memLp_boundedContinuous_mul_fixed_L2
    (μ : Measure R3) (f : Lp ℝ 2 μ) (phi : R3 →ᵇ ℝ) :
    MemLp (fun x => phi x * f x) 2 μ := by
  exact (phi.memLp_top (μ := μ)).mul (Lp.memLp f)

def boundedContinuousMulLpL (μ : Measure R3) (f : Lp ℝ 2 μ) :
    (R3 →ᵇ ℝ) →L[ℝ] Lp ℝ 2 μ :=
  ({ toFun := fun phi => (memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp
         (fun x => phi x * f x)
     map_add' := by
       intro phi psi
       apply Lp.ext
       filter_upwards [(memLp_boundedContinuous_mul_fixed_L2 μ f (phi+psi)).coeFn_toLp,
         (memLp_boundedContinuous_mul_fixed_L2 μ f phi).coeFn_toLp,
         (memLp_boundedContinuous_mul_fixed_L2 μ f psi).coeFn_toLp,
         Lp.coeFn_add ((memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp (fun x => phi x*f x))
           ((memLp_boundedContinuous_mul_fixed_L2 μ f psi).toLp (fun x => psi x*f x))]
         with x hsum hphi hpsi hadd
       rw [hsum,hadd]
       change (phi x+psi x)*f x =
         ((memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp (fun x => phi x*f x)) x +
         ((memLp_boundedContinuous_mul_fixed_L2 μ f psi).toLp (fun x => psi x*f x)) x
       rw [hphi,hpsi]
       ring
     map_smul' := by
       intro c phi
       apply Lp.ext
       filter_upwards [(memLp_boundedContinuous_mul_fixed_L2 μ f (c • phi)).coeFn_toLp,
         (memLp_boundedContinuous_mul_fixed_L2 μ f phi).coeFn_toLp,
         Lp.coeFn_smul c ((memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp (fun x => phi x*f x))]
         with x hsmul hphi hc
       simp only [RingHom.id_apply]
       rw [hsmul,hc]
       change (c*phi x)*f x = c*((memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp (fun x => phi x*f x)) x
       rw [hphi]
       ring } : (R3 →ᵇ ℝ) →ₗ[ℝ] Lp ℝ 2 μ).mkContinuous ‖f‖ (fun phi => by
       have hb : ‖(memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp
           (fun x => phi x*f x)‖ ≤ ‖phi‖*‖f‖ := by
         apply Lp.norm_le_mul_norm_of_ae_le_mul
         filter_upwards [(memLp_boundedContinuous_mul_fixed_L2 μ f phi).coeFn_toLp] with x hx
         rw [hx,norm_mul]
         exact mul_le_mul_of_nonneg_right (phi.norm_coe_le_norm x) (norm_nonneg _)
       change ‖(memLp_boundedContinuous_mul_fixed_L2 μ f phi).toLp
         (fun x => phi x*f x)‖ ≤ ‖f‖*‖phi‖
       exact hb.trans_eq (mul_comm _ _))

theorem boundedContinuousMulLpL_apply_ae
    (μ : Measure R3) (f : Lp ℝ 2 μ) (phi : R3 →ᵇ ℝ) :
    boundedContinuousMulLpL μ f phi =ᵐ[μ] (fun x => phi x * f x) := by
  exact (memLp_boundedContinuous_mul_fixed_L2 μ f phi).coeFn_toLp

theorem norm_boundedContinuousMulLpL_le
    (μ : Measure R3) (f : Lp ℝ 2 μ) :
    ‖boundedContinuousMulLpL μ f‖ ≤ ‖f‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

theorem contDiff_boundedContinuousMulLpL_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (A : P → (R3 →ᵇ ℝ)) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun p => boundedContinuousMulLpL μ f (A p)) := by
  exact (boundedContinuousMulLpL μ f).contDiff.comp hA

theorem hasFDerivAt_boundedContinuousMulLpL_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μ : Measure R3) (f : Lp ℝ 2 μ)
    (A : P → (R3 →ᵇ ℝ)) (dA : P →L[ℝ] (R3 →ᵇ ℝ)) (p : P)
    (hA : HasFDerivAt A dA p) :
    HasFDerivAt (fun q => boundedContinuousMulLpL μ f (A q))
      ((boundedContinuousMulLpL μ f).comp dA) p := by
  exact (boundedContinuousMulLpL μ f).hasFDerivAt.comp p hA

theorem memLp_inverse_norm_on_ball (R : ℝ) :
    MemLp (fun z : R3 => 1 / ‖z‖) 2 (volume.restrict (ball (0 : R3) R)) := by
  have hm : Measurable (fun z : R3 => 1 / ‖z‖) := measurable_const.div continuous_norm.measurable
  have hs : Measurable (fun z : R3 => (1 / ‖z‖)^2) := hm.pow_const 2
  have hi : IntegrableOn (fun z : R3 => (1 / ‖z‖)^2) (ball (0 : R3) R) volume := by
    apply integrableOn_ball_of_norm_le_rpow (μ := volume) (E := R3)
      (C := 1) (α := 2) (by norm_num [R3]) (by norm_num [R3]) _ hs.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),one_mul,
      Real.rpow_neg (norm_nonneg z),Real.rpow_two]
    simp only [one_div,inv_pow]
    exact le_rfl
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable.restrict).mpr hi

theorem memLp_coordinate_pair_inverse_cube_on_ball (R : ℝ) (i j : Fin 3) :
    MemLp (fun z : R3 => z i * z j / ‖z‖^3) 2 (volume.restrict (ball (0 : R3) R)) := by
  have hm : Measurable (fun z : R3 => z i * z j / ‖z‖^3) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).div
      (continuous_norm.measurable.pow_const 3)
  apply (memLp_inverse_norm_on_ball R).mono' hm.aestronglyMeasurable.restrict
  filter_upwards [] with z
  by_cases hz : z = 0
  · subst z
    simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg z) 3)]
  calc
    _ ≤ (‖z‖*‖z‖) / ‖z‖^3 :=
      div_le_div_of_nonneg_right (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) (by positivity)
    _ = 1 / ‖z‖ := by field_simp

theorem memLp_coordinate_quad_inverse_fifth_on_ball (R : ℝ) (i j k l : Fin 3) :
    MemLp (fun z : R3 => z i * z j * z k * z l / ‖z‖^5) 2
      (volume.restrict (ball (0 : R3) R)) := by
  have hm : Measurable (fun z : R3 => z i * z j * z k * z l / ‖z‖^5) :=
    (((((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).mul
      (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable).mul
      (EuclideanSpace.proj (𝕜 := ℝ) l).continuous.measurable).div
      (continuous_norm.measurable.pow_const 5)
  apply (memLp_inverse_norm_on_ball R).mono' hm.aestronglyMeasurable.restrict
  filter_upwards [] with z
  by_cases hz : z = 0
  · subst z
    simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc (a : Fin 3) : |z a| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z a
  have hp (a b : Fin 3) : |z a| * |z b| ≤ ‖z‖*‖z‖ :=
    mul_le_mul (hc a) (hc b) (abs_nonneg _) (norm_nonneg _)
  have hprod : |z i| * |z j| * |z k| * |z l| ≤ ‖z‖^4 := by
    calc
      _ = (|z i| * |z j|)*(|z k| * |z l|) := by ring
      _ ≤ (‖z‖*‖z‖)*(‖z‖*‖z‖) :=
        mul_le_mul (hp i j) (hp k l) (by positivity) (by positivity)
      _ = ‖z‖^4 := by ring
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_mul,abs_mul,
    abs_of_nonneg (pow_nonneg (norm_nonneg z) 5)]
  calc
    _ ≤ ‖z‖^4 / ‖z‖^5 := div_le_div_of_nonneg_right hprod (by positivity)
    _ = 1 / ‖z‖ := by field_simp

end OAI.AnisotropicCalderon.ConnectionError
