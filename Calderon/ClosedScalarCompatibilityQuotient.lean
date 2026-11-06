import Calderon.SmoothKernelCodomainRestriction
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ClosedScalarCompatibility
open SmoothKernelCodomainRestriction
/-! Full upfront EXPANSION-v001.json precedes source. Closure follows from
the original continuous scalar constraints, not a closure assumption. -/
variable {E X I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def simultaneousScalarKernel (ell : I → E →L[ℝ] ℝ) : Submodule ℝ E :=
  ⨅ i, (ell i).ker

lemma mem_simultaneousScalarKernel_iff (ell : I → E →L[ℝ] ℝ) (x : E) :
    x ∈ simultaneousScalarKernel ell ↔ ∀ i, ell i x = 0 := by
  change x ∈ (⨅ i, (ell i).ker) ↔ _
  rw [Submodule.mem_iInf]
  rfl

lemma isClosed_simultaneousScalarKernel (ell : I → E →L[ℝ] ℝ) :
    IsClosed (simultaneousScalarKernel ell : Set E) := by
  rw [simultaneousScalarKernel,Submodule.coe_iInf]
  exact isClosed_iInter (fun i => (ell i).isClosed_ker)

instance simultaneousScalarKernel_isClosed (ell : I → E →L[ℝ] ℝ) :
    IsClosed (simultaneousScalarKernel ell : Set E) :=
  isClosed_simultaneousScalarKernel ell

def scalarCompatibilityQuotientL (ell : I → E →L[ℝ] ℝ) :
    E →L[ℝ] E ⧸ simultaneousScalarKernel ell :=
  (simultaneousScalarKernel ell).mkQL

lemma ker_scalarCompatibilityQuotientL (ell : I → E →L[ℝ] ℝ) :
    (scalarCompatibilityQuotientL ell).ker = simultaneousScalarKernel ell := by
  change LinearMap.ker (simultaneousScalarKernel ell).mkQ = simultaneousScalarKernel ell
  exact Submodule.ker_mkQ _

lemma scalarCompatibilityQuotientL_eq_zero_iff (ell : I → E →L[ℝ] ℝ) (x : E) :
    scalarCompatibilityQuotientL ell x = 0 ↔ ∀ i, ell i x = 0 := by
  change (Submodule.Quotient.mk x : E ⧸ simultaneousScalarKernel ell) = 0 ↔ _
  exact (Submodule.Quotient.mk_eq_zero (p := simultaneousScalarKernel ell) (x := x)).trans
    (mem_simultaneousScalarKernel_iff ell x)

def scalarKernelOfQuotientL (ell : I → E →L[ℝ] ℝ) :
    (scalarCompatibilityQuotientL ell).ker →L[ℝ] simultaneousScalarKernel ell where
  toFun := fun x => ⟨x.1,(mem_simultaneousScalarKernel_iff ell x.1).2
      ((scalarCompatibilityQuotientL_eq_zero_iff ell x.1).1
        (show scalarCompatibilityQuotientL ell x.1 = 0 from x.2))⟩
  map_add' := fun _ _ => Subtype.ext rfl
  map_smul' := fun _ _ => Subtype.ext rfl
  cont := continuous_subtype_val.subtype_mk
    (fun x => (mem_simultaneousScalarKernel_iff ell x.1).2
      ((scalarCompatibilityQuotientL_eq_zero_iff ell x.1).1
        (show scalarCompatibilityQuotientL ell x.1 = 0 from x.2)))

lemma scalarKernelOfQuotientL_apply (ell : I → E →L[ℝ] ℝ)
    (x : (scalarCompatibilityQuotientL ell).ker) :
    (scalarKernelOfQuotientL ell x : E) = x := rfl

def scalarCompatibilityRestriction (ell : I → E →L[ℝ] ℝ) (f : X → E) (s : Set X)
    (hOriginal : ∀ x ∈ s, ∀ i, ell i (f x) = 0) : X → simultaneousScalarKernel ell :=
  fun x => scalarKernelOfQuotientL ell
    (kernelCodomainRestriction (scalarCompatibilityQuotientL ell) f s
      (fun y hy => (scalarCompatibilityQuotientL_eq_zero_iff ell (f y)).2 (hOriginal y hy)) x)

lemma scalarCompatibilityRestriction_coe_of_mem
    (ell : I → E →L[ℝ] ℝ) (f : X → E) (s : Set X)
    (hOriginal : ∀ x ∈ s, ∀ i, ell i (f x) = 0) (x : X) (hx : x ∈ s) :
    (scalarCompatibilityRestriction ell f s hOriginal x : E) = f x := by
  exact kernelCodomainRestriction_coe_of_mem (scalarCompatibilityQuotientL ell) f s
    (fun y hy => (scalarCompatibilityQuotientL_eq_zero_iff ell (f y)).2 (hOriginal y hy)) x hx

lemma contDiffOn_scalarCompatibilityRestriction
    (ell : I → E →L[ℝ] ℝ) (f : X → E) (s : Set X) (hs : IsOpen s)
    (hOriginal : ∀ x ∈ s, ∀ i, ell i (f x) = 0) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (scalarCompatibilityRestriction ell f s hOriginal) s := by
  have hKernel := contDiffOn_kernelCodomainRestriction
    (scalarCompatibilityQuotientL ell) f s hs.uniqueDiffOn hf
      (fun y hy => (scalarCompatibilityQuotientL_eq_zero_iff ell (f y)).2 (hOriginal y hy))
  have hMap : ContDiff ℝ ∞ (scalarKernelOfQuotientL ell :
      (scalarCompatibilityQuotientL ell).ker → simultaneousScalarKernel ell) :=
    (scalarKernelOfQuotientL ell).contDiff
  exact ContDiff.comp_contDiffOn hMap hKernel

#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.simultaneousScalarKernel
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.mem_simultaneousScalarKernel_iff
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.isClosed_simultaneousScalarKernel
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.simultaneousScalarKernel_isClosed
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarCompatibilityQuotientL
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.ker_scalarCompatibilityQuotientL
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarCompatibilityQuotientL_eq_zero_iff
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarKernelOfQuotientL
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarKernelOfQuotientL_apply
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarCompatibilityRestriction
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.scalarCompatibilityRestriction_coe_of_mem
#print axioms OAI.AnisotropicCalderon.ClosedScalarCompatibility.contDiffOn_scalarCompatibilityRestriction
end OAI.AnisotropicCalderon.ClosedScalarCompatibility
