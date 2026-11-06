import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Reduction of the native implicit function theorem. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exists_joint_local_parameter_inverse (f : P × V → V)
    (hf : ContDiff ℝ ∞ f) (p0 : P) (z0 : V)
    (hD : ((fderiv ℝ f (p0,z0)).comp (ContinuousLinearMap.inr ℝ P V)).IsInvertible) :
    ∃ ψ : P × V → V, ContDiffAt ℝ ∞ ψ (p0,f (p0,z0)) ∧
      ψ (p0,f (p0,z0)) = z0 ∧
      (∀ᶠ b in 𝓝 (p0,f (p0,z0)), f (b.1,ψ b) = b.2) ∧
      ∀ᶠ b : (P × V) × V in 𝓝 ((p0,f (p0,z0)),z0),
        f (b.1.1,b.2) = b.1.2 ↔ ψ b.1 = b.2 := by
  let H : (P × V) × V → V := fun b => f (b.1.1,b.2) - b.1.2
  let p : P × V := (p0,f (p0,z0))
  let u : (P × V) × V := (p,z0)
  have hH : ContDiff ℝ ∞ H :=
    (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  have hHs : HasFDerivAt (fun z => H (p,z))
      ((fderiv ℝ H u).comp (ContinuousLinearMap.inr ℝ (P × V) V)) z0 :=
    (hH.differentiable (by simp) u).hasFDerivAt.comp z0 (hasFDerivAt_prodMk_right p z0)
  have hfs : HasFDerivAt (fun z => f (p0,z) - f (p0,z0))
      ((fderiv ℝ f (p0,z0)).comp (ContinuousLinearMap.inr ℝ P V)) z0 := by
    simpa only [Pi.sub_def,Pi.sub_apply,Function.comp_apply,sub_zero] using
      ((hf.differentiable (by simp) (p0,z0)).hasFDerivAt.comp z0
        (hasFDerivAt_prodMk_right p0 z0)).sub (hasFDerivAt_const (f (p0,z0)) z0)
  have heq : ((fderiv ℝ H u).comp (ContinuousLinearMap.inr ℝ (P × V) V)) =
      ((fderiv ℝ f (p0,z0)).comp (ContinuousLinearMap.inr ℝ P V)) :=
    hHs.unique hfs
  have hInv : ((fderiv ℝ H u).comp (ContinuousLinearMap.inr ℝ (P × V) V)).IsInvertible := by
    rw [heq]
    exact hD
  let cdf : ContDiffAt ℝ ∞ H u := hH.contDiffAt
  let ψ : P × V → V := cdf.implicitFunction (by simp) hInv
  refine ⟨ψ,cdf.contDiffAt_implicitFunction (by simp) hInv,
    cdf.implicitFunction_apply_self (by simp) hInv,?_,?_⟩
  · filter_upwards [cdf.eventually_apply_implicitFunction (by simp) hInv] with b hb
    have hz : f (b.1,ψ b) - b.2 = 0 := by
      simpa only [H,u,p,sub_self] using hb
    exact sub_eq_zero.mp hz
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction (by simp) hInv] with b hb
    simpa only [H,u,p,sub_self,sub_eq_zero] using hb

end OAI.AnisotropicCalderon.ConnectionError
