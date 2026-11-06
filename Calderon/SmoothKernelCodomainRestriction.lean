import Calderon.LinearIsometryTaylorReflection

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.LinearIsometryTaylorReflection
namespace OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDerivWithin_mem_kernel
    (C : F →L[ℝ] G) (f : E → F) (s : Set E)
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hz : ∀ x ∈ s, C (f x) = 0) (m : ℕ) (x : E) (hx : x ∈ s)
    (v : Fin m → E) : iteratedFDerivWithin ℝ m f s x v ∈ C.ker := by
  have heq : EqOn (C ∘ f) (fun _ : E => (0 : G)) s := hz
  have hzero : iteratedFDerivWithin ℝ m (C ∘ f) s x = 0 := by
    rw [iteratedFDerivWithin_congr heq hx m]
    exact congrFun (iteratedFDerivWithin_fun_zero (𝕜 := ℝ) (s := s) (i := m)) x
  have hc : C.compContinuousMultilinearMap (iteratedFDerivWithin ℝ m f s x) = 0 :=
    (C.iteratedFDerivWithin_comp_left (hf x hx) hs hx (by simp)).symm.trans hzero
  change C (iteratedFDerivWithin ℝ m f s x v) = 0
  exact congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) G => A v) hc

def kernelCodomainRestriction
    (C : F →L[ℝ] G) (f : E → F) (s : Set E) (hz : ∀ x ∈ s, C (f x) = 0) : E → C.ker := by
  classical
  exact fun x => if hx : x ∈ s then ⟨f x,hz x hx⟩ else 0

theorem kernelCodomainRestriction_coe_of_mem
    (C : F →L[ℝ] G) (f : E → F) (s : Set E) (hz : ∀ x ∈ s, C (f x) = 0)
    (x : E) (hx : x ∈ s) :
    (kernelCodomainRestriction C f s hz x : F) = f x := by
  simp only [kernelCodomainRestriction,dif_pos hx]

theorem contDiffOn_kernelCodomainRestriction
    (C : F →L[ℝ] G) (f : E → F) (s : Set E)
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ ∞ f s)
    (hz : ∀ x ∈ s, C (f x) = 0) :
    ContDiffOn ℝ ∞ (kernelCodomainRestriction C f s hz) s := by
  classical
  let p : E → FormalMultilinearSeries ℝ E C.ker := fun x m =>
    if hx : x ∈ s then
      (iteratedFDerivWithin ℝ m f s x).codRestrict C.ker
        (iteratedFDerivWithin_mem_kernel C f s hs hf hz m x hx)
    else 0
  let I : C.ker →ₗᵢ[ℝ] F := C.ker.subtypeₗᵢ
  have hp (m : ℕ) (x : E) (hx : x ∈ s) :
      I.toContinuousLinearMap.compContinuousMultilinearMap (p x m) =
        ftaylorSeriesWithin ℝ f s x m := by
    dsimp only [p]
    rw [dif_pos hx]
    apply ContinuousMultilinearMap.ext
    intro v
    rfl
  have hv (x : E) (hx : x ∈ s) :
      (I ∘ kernelCodomainRestriction C f s hz) x = f x :=
    kernelCodomainRestriction_coe_of_mem C f s hz x hx
  have ht : HasFTaylorSeriesUpToOn (∞ : ℕ∞ω)
      (I ∘ kernelCodomainRestriction C f s hz)
      (fun x m => I.toContinuousLinearMap.compContinuousMultilinearMap (p x m)) s := by
    apply ((hf.ftaylorSeriesWithin hs).congr hv).congr_series
    intro m hm x hx
    exact (hp m x hx).symm
  exact (hasFTaylorSeriesUpToOn_of_linearIsometry_comp I (∞ : ℕ∞ω)
    (kernelCodomainRestriction C f s hz) p s ht).contDiffOn

end OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
