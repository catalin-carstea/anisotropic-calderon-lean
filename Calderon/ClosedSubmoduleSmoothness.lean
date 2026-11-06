import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
noncomputable section
open Set Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_mem_closed_submodule (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → F) (hf : ∀ x, f x ∈ S) (x h : E) (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x h ∈ S := by
  let c : ℝ → F := fun r => f (x+r • h)
  have hc : HasDerivAt c (fderiv ℝ f x h) 0 := by
    have hp : HasDerivAt (fun r : ℝ => x+r • h) h 0 := by
      have hp0 := (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const h)
      change HasDerivAt (fun r : ℝ => x+r • h) ((0 : E)+(1 : ℝ) • h) 0 at hp0
      simpa only [zero_add,one_smul] using hp0
    simpa only [c,Function.comp_def,zero_smul,add_zero] using
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hm : deriv c 0 ∈ closure (Submodule.span ℝ (c '' (univ : Set ℝ)) : Set F) :=
    range_deriv_subset_closure_span_image c dense_univ ⟨0,rfl⟩
  have hs : closure (Submodule.span ℝ (c '' (univ : Set ℝ)) : Set F) ⊆ S := by
    apply closure_minimal _ hS
    exact Submodule.span_le.mpr (by rintro _ ⟨r,_,rfl⟩; exact hf (x+r • h))
  rw [hc.deriv] at hm
  exact hs hm

theorem differentiable_closed_submodule (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) (hf : Differentiable ℝ (fun x => (f x : F))) : Differentiable ℝ f := by
  have hcont : Continuous f := continuous_induced_rng.mpr hf.continuous
  intro x
  let d : E →L[ℝ] S := (fderiv ℝ (fun y => (f y : F)) x).codRestrict S
    (fun h => fderiv_mem_closed_submodule S hS _ (fun y => (f y).property) x h (hf x))
  have hd : HasFDerivAt (fun y => (f y : F)) (S.subtypeL.comp d) x := by
    simpa only [d,ContinuousLinearMap.subtypeL_comp_codRestrict] using (hf x).hasFDerivAt
  exact (HasFDerivAt.of_comp_of_isEmbedding (hcont.continuousAt)
    (S.subtypeL.hasFDerivAt) Topology.IsEmbedding.subtypeVal hd (Filter.Eventually.of_forall
      (fun _ => rfl))).differentiableAt

theorem contDiff_nat_closed_submodule [FiniteDimensional ℝ E]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F)) (n : ℕ) (f : E → S)
    (hf : ContDiff ℝ n (fun x => (f x : F))) : ContDiff ℝ n f := by
  induction n generalizing f with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_induced_rng.mpr hf.continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hf ⊢
    have hdf : Differentiable ℝ f := differentiable_closed_submodule S hS f
      (hf.differentiable (by simp))
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨hdf,?_,?_⟩
    · intro h
      simp at h
    · intro v
      apply ih (fun x => fderiv ℝ f x v)
      have he : (fun x => ((fderiv ℝ f x v : S) : F)) =
          (fun x => fderiv ℝ (fun y => (f y : F)) x v) := by
        funext x
        have hd := (S.subtypeL.hasFDerivAt).comp x (hdf x).hasFDerivAt
        change HasFDerivAt (fun y => (f y : F)) (S.subtypeL.comp (fderiv ℝ f x)) x at hd
        exact (congrArg (fun L : E →L[ℝ] F => L v) hd.fderiv).symm
      rw [he]
      exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_infty_closed_submodule [FiniteDimensional ℝ E]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F)) (f : E → S)
    (hf : ContDiff ℝ ∞ (fun x => (f x : F))) : ContDiff ℝ ∞ f := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_closed_submodule S hS n f (contDiff_infty.mp hf n)
end OAI.AnisotropicCalderon.DirichletFamily
