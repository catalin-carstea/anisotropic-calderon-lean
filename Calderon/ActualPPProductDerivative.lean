import Calderon.ActualHigherSCoefficientExtraction

/-! Author source, UNCOMPILED. Upfront: pp-upfront-v001/UPFRONT.md.
This expands the exact typed Hi→Half→Neg coefficient composition derivative.
No analytic estimate, inverse inclusion or full-output adjunction is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPProductDerivative
open PrincipalCommutator ActualHigherSCoefficientExtraction
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Differentiate an actual low-after-high product at a point. This supplies
both coefficient-derivative rows of each Green remainder, in literal order. -/
theorem directional_composition_apply_at
    (L : R3 → H →L[ℝ] N) (A : R3 → E →L[ℝ] H) (x X : R3)
    (hL : DifferentiableAt ℝ L x) (hA : DifferentiableAt ℝ A x) (v : E) :
    (directionalFDeriv X (fun y => (L y).comp (A y)) x) v =
      (directionalFDeriv X L x) (A x v)+L x ((directionalFDeriv X A x) v) := by
  have hC : DifferentiableAt ℝ (fun y => (L y).comp (A y)) x := hL.clm_comp hA
  have hAv : DifferentiableAt ℝ (fun y => A y v) x := hA.clm_apply (differentiableAt_const v)
  have hAvD : fderiv ℝ (fun y => A y v) x X = (directionalFDeriv X A x) v := by
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,zero_add] using
      fderiv_family_apply_point A (fun _ : R3 => v) x X hA (differentiableAt_const v)
  have hEval : fderiv ℝ (fun y => ((L y).comp (A y)) v) x X =
      (directionalFDeriv X (fun y => (L y).comp (A y)) x) v := by
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,zero_add] using
      fderiv_family_apply_point (fun y => (L y).comp (A y))
        (fun _ : R3 => v) x X hC (differentiableAt_const v)
  calc
    _ = fderiv ℝ (fun y => L y (A y v)) x X := hEval.symm
    _ = L x (fderiv ℝ (fun y => A y v) x X)+
        (fderiv ℝ L x X) (A x v) :=
      fderiv_family_apply_point L (fun y => A y v) x X hL hAv
    _ = L x ((directionalFDeriv X A x) v)+
        (directionalFDeriv X L x) (A x v) := by rw [hAvD]; rfl
    _ = _ := add_comm _ _
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPProductDerivative
