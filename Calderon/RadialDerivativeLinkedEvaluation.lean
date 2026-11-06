import Calderon.LocalRadialDerivative

set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P E X V W : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem radialFirstDerivative_eq_of_linked_evaluation
    (F : P × ℝ → E →L[ℝ] W) (G : P × ℝ → X →L[ℝ] V)
    (Z : V →L[ℝ] W) (y : P) (e : E) (x : X)
    (hF : DifferentiableAt ℝ F (y,0)) (hG : DifferentiableAt ℝ G (y,0))
    (hEq : (fun r : ℝ => F (y,r) e) =ᶠ[𝓝 0] (fun r : ℝ => Z (G (y,r) x))) :
    radialFirstDerivative F (y,0) e = Z (radialFirstDerivative G (y,0) x) := by
  have hc : HasDerivAt (fun r : ℝ => (y,r)) (0,1) 0 :=
    (hasDerivAt_const 0 y).prodMk (hasDerivAt_id 0)
  have hFd : HasDerivAt (fun r : ℝ => F (y,r)) (radialFirstDerivative F (y,0)) 0 := by
    simpa only [Function.comp_def,radialFirstDerivative] using
      hF.hasFDerivAt.comp_hasDerivAt 0 hc
  have hGd : HasDerivAt (fun r : ℝ => G (y,r)) (radialFirstDerivative G (y,0)) 0 := by
    simpa only [Function.comp_def,radialFirstDerivative] using
      hG.hasFDerivAt.comp_hasDerivAt 0 hc
  have he := hFd.clm_apply (hasDerivAt_const (0 : ℝ) e)
  have hx := hGd.clm_apply (hasDerivAt_const (0 : ℝ) x)
  simp only [map_zero,add_zero,zero_add] at he hx
  have hz : HasDerivAt (fun r : ℝ => Z (G (y,r) x))
      (Z (radialFirstDerivative G (y,0) x)) 0 :=
    Z.hasFDerivAt.comp_hasDerivAt 0 hx
  exact he.unique (hz.congr_of_eventuallyEq hEq)

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.radialFirstDerivative_eq_of_linked_evaluation
