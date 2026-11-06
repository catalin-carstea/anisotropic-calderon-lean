import Calderon.MetricHessianTestEquiv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra

/-- The ordinary curried Hessian commutes with subtraction of smooth germs. -/
theorem fderiv_fderiv_fun_sub_of_contDiffAt
    (f g : R3 → ℝ) (x : R3)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    fderiv ℝ (fderiv ℝ (fun z : R3 => f z - g z)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hfNear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 f y :=
    (hf.of_le (m := 1) (by simp)).eventually (by simp)
  have hgNear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 g y :=
    (hg.of_le (m := 1) (by simp)).eventually (by simp)
  have hGerm : fderiv ℝ (fun z : R3 => f z - g z) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y - fderiv ℝ g y) := by
    filter_upwards [hfNear, hgNear] with y hfy hgy
    exact fderiv_fun_sub hfy.differentiableAt_one hgy.differentiableAt_one
  have hDf := hf.fderiv_right (m := ∞) (by simp)
  have hDg := hg.fderiv_right (m := ∞) (by simp)
  calc
    fderiv ℝ (fderiv ℝ (fun z : R3 => f z - g z)) x =
        fderiv ℝ (fun y => fderiv ℝ f y - fderiv ℝ g y) x :=
      hGerm.fderiv_eq (𝕜 := ℝ)
    _ = fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x :=
      fderiv_fun_sub (hDf.differentiableAt (by simp)) (hDg.differentiableAt (by simp))

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
