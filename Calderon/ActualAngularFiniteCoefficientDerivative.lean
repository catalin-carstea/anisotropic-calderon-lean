import Calderon.PrincipalDirectional
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualAngularFiniteCoefficientDerivative
open PrincipalCommutator

lemma directionalFDeriv_finite_sum
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → R3 → E) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (X x : R3) :
    directionalFDeriv X (fun y => ∑ i : ι, f i y) x =
      ∑ i : ι, directionalFDeriv X (f i) x := by
  unfold directionalFDeriv
  rw [fderiv_fun_sum (fun i _ => (hf i).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply]


lemma directionalFDeriv_fixed_scalar_sum
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (T : ι → E) (X x : R3) :
    directionalFDeriv X (fun y => r • ∑ i : ι, c i y • T i) x =
      r • ∑ i : ι, directionalFDeriv X (c i) x • T i := by
  have hs : ContDiff ℝ ∞ (fun y => ∑ i : ι, c i y • T i) :=
    ContDiff.sum (fun i _ => (hc i).smul contDiff_const)
  have hconstR : directionalFDeriv X (fun _ : R3 => r) x=0 := by
    simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply]
  rw [directionalFDeriv_smul X (fun _ : R3 => r) _ contDiff_const hs x,hconstR,zero_smul,zero_add]
  rw [directionalFDeriv_finite_sum (fun i y => c i y • T i)
    (fun i => (hc i).smul contDiff_const) X x]
  apply congrArg (fun z : E => r • z)
  apply Finset.sum_congr rfl
  intro i hi
  have hconstT : directionalFDeriv X (fun _ : R3 => T i) x=0 := by
    simp only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply]
  rw [directionalFDeriv_smul X (c i) (fun _ : R3 => T i) (hc i) contDiff_const x,
    hconstT,smul_zero,add_zero]

end OAI.AnisotropicCalderon.ActualAngularFiniteCoefficientDerivative
