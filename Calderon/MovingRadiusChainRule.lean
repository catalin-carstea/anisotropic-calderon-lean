import Calderon.ActualPhysicalBoundaryChainRule
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Source-only generic radius-profile chain rule. The physical profile
expansion and literal interfaces were sealed before proof source. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem fderiv_movingRadius_comp
    (f : (R3 × ℝ) × R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y z X W : R3) :
    fderiv ℝ (fun p : R3 × R3 => f ((p.1,R p.1),p.2)) (y,z) (X,W) =
      fderiv ℝ (fun p : R3 × R3 => f ((p.1,R y),p.2)) (y,z) (X,W) +
        fderiv ℝ R y X * deriv (fun r : ℝ => f ((y,r),z)) (R y) := by
  let A : (R3 × R3) →L[ℝ] R3 := ContinuousLinearMap.fst ℝ R3 R3
  let B : (R3 × R3) →L[ℝ] R3 := ContinuousLinearMap.snd ℝ R3 R3
  let dR : R3 →L[ℝ] ℝ := fderiv ℝ R y
  let dF : ((R3 × ℝ) × R3) →L[ℝ] ℝ := fderiv ℝ f ((y,R y),z)
  have hfst : HasFDerivAt (fun p : R3 × R3 => p.1) A (y,z) :=
    hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z))
  have hsnd : HasFDerivAt (fun p : R3 × R3 => p.2) B (y,z) :=
    hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z))
  have hRp : HasFDerivAt (fun p : R3 × R3 => R p.1) (dR.comp A) (y,z) :=
    (hR.differentiable (by simp) y).hasFDerivAt.comp (y,z) hfst
  have hS : HasFDerivAt (fun p : R3 × R3 => ((p.1,R p.1),p.2))
      ((A.prod (dR.comp A)).prod B) (y,z) := (hfst.prodMk hRp).prodMk hsnd
  have hS0 : HasFDerivAt (fun p : R3 × R3 => ((p.1,R y),p.2))
      ((A.prod 0).prod B) (y,z) :=
    (hfst.prodMk (hasFDerivAt_const (R y) (y,z))).prodMk hsnd
  have hF : HasFDerivAt f dF ((y,R y),z) :=
    (hf.differentiable (by simp) ((y,R y),z)).hasFDerivAt
  have hMoving := hF.comp (y,z) hS
  have hFixed := hF.comp (y,z) hS0
  have hCurve : HasDerivAt (fun r : ℝ => ((y,r),z)) (((0 : R3),1),(0 : R3)) (R y) :=
    ((hasDerivAt_const (R y) y).prodMk (hasDerivAt_id (R y))).prodMk
      (hasDerivAt_const (R y) z)
  have hRadial := hF.comp_hasDerivAt (R y) hCurve
  change fderiv ℝ (f ∘ (fun p : R3 × R3 => ((p.1,R p.1),p.2))) (y,z) (X,W) =
    fderiv ℝ (f ∘ (fun p : R3 × R3 => ((p.1,R y),p.2))) (y,z) (X,W) +
      fderiv ℝ R y X * deriv (f ∘ (fun r : ℝ => ((y,r),z))) (R y)
  rw [hMoving.fderiv,hFixed.fderiv,hRadial.deriv]
  change dF ((X,dR X),W) = dF ((X,0),W) + dR X * dF (((0 : R3),1),(0 : R3))
  have heq : ((X,dR X),W) = ((X,0),W) +
      dR X • (((0 : R3),(1 : ℝ)),(0 : R3)) := by
    simp only [Prod.mk_add_mk,Prod.smul_mk,smul_zero,smul_eq_mul,mul_one,add_zero,zero_add]
  rw [heq,map_add,map_smul]
  rfl

theorem fderiv_log_radius_apply (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y X : R3) (hy : R y ≠ 0) :
    fderiv ℝ (fun x => Real.log (R x)) y X = (R y)⁻¹ * fderiv ℝ R y X := by
  rw [((hR.differentiable (by simp) y).hasFDerivAt.log hy).fderiv]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
