import Calderon.SecondFlowVariation

set_option autoImplicit false
noncomputable section
open scoped ContDiff NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem inhomogeneous_nilpotent_solution (L : E →L[ℝ] E) (C : E)
    (hLC : L (L C) = 0) (W : ℝ → E) (hW : ∀ t, HasDerivAt W (L (W t) + C) t)
    (hW0 : W 0 = 0) (t : ℝ) : W t = t • C + (t^2/2) • L C := by
  let P : ℝ → E := fun s => s • C + (s^2/2) • L C
  have hP : ∀ s, HasDerivAt P (L (P s) + C) s := by
    intro s
    have hs : HasDerivAt (fun r : ℝ => r^2/2) s s := by
      convert ((hasDerivAt_id s).pow 2).div_const 2 using 1 <;>
        simp [id_eq, Pi.pow_apply] <;> ring
    have hd := ((hasDerivAt_id s).smul_const C).add (hs.smul_const (L C))
    simp only [one_smul] at hd
    change HasDerivAt P (C + s • L C) s at hd
    exact hd.congr_deriv (by simp [P,map_add,map_smul,hLC,add_comm])
  have hZ : ∀ s, HasDerivAt (fun r => W r - P r) (L (W s - P s)) s := by
    intro s
    have hd := (hW s).sub (hP s)
    exact hd.congr_deriv (by rw [map_sub]; abel)
  have hZ0 : W 0 - P 0 = 0 := by simp [P,hW0]
  have he := ODE.eq_globalSolution L L.lipschitzWith hZ
  rw [hZ0] at he
  have hz := congrFun he t
  rw [globalSolution_stationary L L.lipschitzWith 0 (map_zero L) t] at hz
  exact sub_eq_zero.mp hz

theorem globalSolution_secondBaseVariation_nilpotent (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a : E) (ha : v a = 0)
    (hnil : ∀ d, fderiv ℝ v a (fderiv ℝ v a d) = 0) (h k C : E)
    (hforce : ∀ t : ℝ, fderiv ℝ (fderiv ℝ v) a
      (k + t • fderiv ℝ v a k) (h + t • fderiv ℝ v a h) = C) (t : ℝ) :
    flowSecondBaseVariation v hv h k (a,t) =
      t • C + (t^2/2) • fderiv ℝ v a C := by
  let L := fderiv ℝ v a
  let W : ℝ → E := fun s => flowSecondBaseVariation v hv h k (a,s)
  have hJ (d : E) (s : ℝ) : flowBaseVariation v hv d (a,s) = d + s • L d :=
    globalSolution_baseDerivative_nilpotent v hv hvs a ha hnil d s
  have hW : ∀ s, HasDerivAt W (L (W s) + C) s := by
    intro s
    have hd := hasDerivAt_flowSecondBaseVariation v hv hvs a h k s
    simp only [globalSolution_stationary v hv a ha,hJ k s,hJ h s] at hd
    dsimp [L] at hd
    rw [hforce s] at hd
    exact hd
  exact inhomogeneous_nilpotent_solution L C (hnil C) W hW
    (flowSecondBaseVariation_zero v hv hvs a h k) t
end OAI.AnisotropicCalderon.ConnectionError
