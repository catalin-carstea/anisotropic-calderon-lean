import Calderon.ParameterHadamardDivision
import Calderon.SmoothSignedTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

universe u
variable {P V : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

local instance spatialFirstNormedGroup : NormedAddCommGroup (R3 →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance spatialFirstNormedSpace : NormedSpace ℝ (R3 →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
local instance spatialFirstComplete : CompleteSpace (R3 →L[ℝ] V) :=
  ContinuousLinearMap.instCompleteSpace
local instance spatialSecondNormedGroup : NormedAddCommGroup (R3 →L[ℝ] R3 →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance spatialSecondNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3 →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
local instance spatialSecondComplete : CompleteSpace (R3 →L[ℝ] R3 →L[ℝ] V) :=
  ContinuousLinearMap.instCompleteSpace

def spatialDerivative (a : P × R3 → V) (x : P × R3) : R3 →L[ℝ] V :=
  fderiv ℝ (fun z : R3 => a (x.1,z)) x.2

def spatialHessian (a : P × R3 → V) (x : P × R3) : R3 →L[ℝ] R3 →L[ℝ] V :=
  spatialDerivative (spatialDerivative a) x

def spatialSecondTaylorTensor (a : P × R3 → V) (x : P × R3) : R3 →L[ℝ] R3 →L[ℝ] V :=
  ∫ t : ℝ in (0 : ℝ)..1, (1-t) • spatialHessian a (x.1,t • x.2)

def spatialFirstDerivativeRemainderTensor (a : P × R3 → V) (x : P × R3) :
    R3 →L[ℝ] R3 →L[ℝ] V :=
  ∫ t : ℝ in (0 : ℝ)..1, spatialHessian a (x.1,t • x.2)

theorem contDiff_spatialDerivative (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialDerivative a) := by
  have hEq : spatialDerivative a = fun x : P × R3 =>
      (fderiv ℝ a x).comp (ContinuousLinearMap.inr ℝ P R3) := by
    funext x
    exact ((ha.differentiable (by simp) x).hasFDerivAt.comp x.2
      (hasFDerivAt_prodMk_right x.1 x.2)).fderiv
  rw [hEq]
  exact (ha.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem contDiff_spatialHessian (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialHessian a) := by
  exact contDiff_spatialDerivative (spatialDerivative a) (contDiff_spatialDerivative a ha)

theorem contDiff_spatialSecondTaylorTensor (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialSecondTaylorTensor a) := by
  let F : (P × R3) × ℝ → R3 →L[ℝ] R3 →L[ℝ] V :=
    fun x => (1-x.2) • spatialHessian a (x.1.1,x.2 • x.1.2)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_const.sub contDiff_snd).smul
      ((contDiff_spatialHessian a ha).comp
        (contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd)))
  exact contDiff_parameter_unitInterval_integral F hF

theorem contDiff_spatialFirstDerivativeRemainderTensor
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialFirstDerivativeRemainderTensor a) := by
  let F : (P × R3) × ℝ → R3 →L[ℝ] R3 →L[ℝ] V :=
    fun x => spatialHessian a (x.1.1,x.2 • x.1.2)
  have hF : ContDiff ℝ ∞ F := (contDiff_spatialHessian a ha).comp
    (contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd))
  exact contDiff_parameter_unitInterval_integral F hF

private theorem hasDerivAt_spatialDerivative_line
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) (p : P) (z : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => spatialDerivative a (p,s • z))
      (spatialHessian a (p,t • z) z) t := by
  have hSlice : ContDiff ℝ ∞ (fun w : R3 => spatialDerivative a (p,w)) :=
    (contDiff_spatialDerivative a ha).comp (contDiff_const.prodMk contDiff_id)
  have hD := (hSlice.differentiable (by simp) (t • z)).hasFDerivAt
  have hCurve : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  exact hD.comp_hasDerivAt t hCurve

private theorem deriv_spatialLine
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) (p : P) (z : R3) (t : ℝ) :
    deriv (fun s : ℝ => a (p,s • z)) t = spatialDerivative a (p,t • z) z := by
  have hSlice : ContDiff ℝ ∞ (fun w : R3 => a (p,w)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hCurve : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  exact ((hSlice.differentiable (by simp) (t • z)).hasFDerivAt.comp_hasDerivAt t hCurve).deriv

private theorem deriv_deriv_spatialLine
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) (p : P) (z : R3) (t : ℝ) :
    deriv (deriv (fun s : ℝ => a (p,s • z))) t = spatialHessian a (p,t • z) z z := by
  have hFirst : deriv (fun s : ℝ => a (p,s • z)) =
      (fun s : ℝ => spatialDerivative a (p,s • z) z) := by
    funext s
    exact deriv_spatialLine a ha p z s
  rw [hFirst]
  have h := (hasDerivAt_spatialDerivative_line a ha p z t).clm_apply (hasDerivAt_const t z)
  simpa only [map_zero, zero_add, add_zero, Function.comp_def] using h.deriv

theorem eq_spatialSecondTaylorTensor
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) (p : P) (z : R3) :
    a (p,z) = a (p,0) + fderiv ℝ (fun w : R3 => a (p,w)) 0 z +
      spatialSecondTaylorTensor a (p,z) z z := by
  let F : ℝ → V := fun t => a (p,t • z)
  have hF : ContDiff ℝ ∞ F := ha.comp (contDiff_const.prodMk (contDiff_id.smul contDiff_const))
  have hC : Continuous (fun t : ℝ => (1-t) • spatialHessian a (p,t • z)) :=
    (continuous_const.sub continuous_id).smul
      ((contDiff_spatialHessian a ha).continuous.comp
        (continuous_const.prodMk (continuous_id.smul continuous_const)))
  have hInt : IntervalIntegrable
      (fun t : ℝ => (1-t) • spatialHessian a (p,t • z)) volume 0 1 :=
    hC.intervalIntegrable 0 1
  have hIntEval : IntervalIntegrable
      (fun t : ℝ => ((1-t) • spatialHessian a (p,t • z)) z) volume 0 1 :=
    (hC.clm_apply continuous_const).intervalIntegrable 0 1
  have hEval : spatialSecondTaylorTensor a (p,z) z z = secondTaylorRemainder F 1 := by
    rw [spatialSecondTaylorTensor,
      ContinuousLinearMap.intervalIntegral_apply hInt z,
      ContinuousLinearMap.intervalIntegral_apply hIntEval z]
    unfold secondTaylorRemainder
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [ContinuousLinearMap.smul_apply, mul_one]
    rw [show deriv (deriv F) t = spatialHessian a (p,t • z) z z from
      deriv_deriv_spatialLine a ha p z t]
  have hTaylor := signed_taylor_integral_remainder F 1 (fun t _ => hF.contDiffAt)
  have hFirst : deriv F 0 = spatialDerivative a (p,0) z := by
    simpa only [zero_smul] using deriv_spatialLine a ha p z 0
  simp only [F, one_smul, zero_smul, one_pow, hFirst] at hTaylor
  rw [← hEval] at hTaylor
  exact hTaylor

theorem fderiv_eq_spatialFirstDerivativeRemainderTensor
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) (p : P) (z : R3) :
    fderiv ℝ (fun w : R3 => a (p,w)) z =
      fderiv ℝ (fun w : R3 => a (p,w)) 0 + spatialFirstDerivativeRemainderTensor a (p,z) z := by
  have hC : Continuous (fun t : ℝ => spatialHessian a (p,t • z)) :=
    (contDiff_spatialHessian a ha).continuous.comp
      (continuous_const.prodMk (continuous_id.smul continuous_const))
  have hInt : IntervalIntegrable
      (fun t : ℝ => spatialHessian a (p,t • z)) volume 0 1 :=
    hC.intervalIntegrable 0 1
  have hIntEval : IntervalIntegrable
      (fun t : ℝ => spatialHessian a (p,t • z) z) volume 0 1 :=
    (hC.clm_apply continuous_const).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => hasDerivAt_spatialDerivative_line a ha p z t) hIntEval
  simp only [one_smul, zero_smul] at hFTC
  have hEval : spatialFirstDerivativeRemainderTensor a (p,z) z =
      ∫ t : ℝ in (0 : ℝ)..1, spatialHessian a (p,t • z) z :=
    ContinuousLinearMap.intervalIntegral_apply hInt z
  rw [← hEval] at hFTC
  change spatialDerivative a (p,z) = spatialDerivative a (p,0) +
    spatialFirstDerivativeRemainderTensor a (p,z) z
  rw [hFTC]
  abel

theorem spatialSecondTaylorTensor_zero (a : P × R3 → V) (p : P) :
    spatialSecondTaylorTensor a (p,0) = (1/2 : ℝ) • spatialHessian a (p,0) := by
  simp only [spatialSecondTaylorTensor, smul_zero]
  rw [intervalIntegral.integral_smul_const,
    intervalIntegral.integral_sub
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 1), integral_one, integral_id]
  norm_num

theorem spatialFirstDerivativeRemainderTensor_zero (a : P × R3 → V) (p : P) :
    spatialFirstDerivativeRemainderTensor a (p,0) = spatialHessian a (p,0) := by
  simp only [spatialFirstDerivativeRemainderTensor, smul_zero,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem exists_smooth_spatial_quadratic_factorization
    (a : P × R3 → V) (ha : ContDiff ℝ ∞ a) :
    ∃ T U : P × R3 → R3 →L[ℝ] R3 →L[ℝ] V,
      ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ U ∧
      (∀ p : P, ∀ z : R3, a (p,z) = a (p,0) +
        fderiv ℝ (fun w : R3 => a (p,w)) 0 z + T (p,z) z z) ∧
      ∀ p : P, ∀ z : R3, fderiv ℝ (fun w : R3 => a (p,w)) z =
        fderiv ℝ (fun w : R3 => a (p,w)) 0 + U (p,z) z := by
  exact ⟨spatialSecondTaylorTensor a, spatialFirstDerivativeRemainderTensor a,
    contDiff_spatialSecondTaylorTensor a ha, contDiff_spatialFirstDerivativeRemainderTensor a ha,
    eq_spatialSecondTaylorTensor a ha, fderiv_eq_spatialFirstDerivativeRemainderTensor a ha⟩

end OAI.AnisotropicCalderon.ConnectionError
