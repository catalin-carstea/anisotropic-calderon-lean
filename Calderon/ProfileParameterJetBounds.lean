import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon

/-- The actual independent-dual-parameter map needs only three radius jets.
The weights here are pointwise constants; no derivative of beta is taken. -/
theorem profile_parameter_map_jet_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E → ℝ) (hR : ContDiff ℝ ∞ R) (q : ℝ) (y : E)
    (beta C2 C3 : ℝ) (hbeta : 1 ≤ beta)
    (h1 : ‖fderiv ℝ R y‖ ≤ 1)
    (h2 : ‖iteratedFDeriv ℝ 2 R y‖ ≤ C2)
    (h3 : ‖iteratedFDeriv ℝ 3 R y‖ ≤ C3 * beta) :
    let tR : E → (ℝ × (E × ℝ)) × (E →L[ℝ] ℝ) :=
      fun z => ((q,(z,R z)), fderiv ℝ R z)
    ContDiff ℝ ∞ tR ∧
      ‖iteratedFDeriv ℝ 1 tR y‖ ≤ max 1 C2 ∧
      ‖iteratedFDeriv ℝ 2 tR y‖ ≤ max C2 C3 * beta := by
  intro tR
  have hdR : ContDiff ℝ ∞ (fderiv ℝ R) := hR.fderiv_right (by simp)
  have hid : ContDiff ℝ ∞ (fun z : E => z) := contDiff_id
  have hqy : ContDiff ℝ ∞ (fun z : E => (q,(z,R z))) :=
    contDiff_const.prodMk (hid.prodMk hR)
  have ht : ContDiff ℝ ∞ tR := hqy.prodMk hdR
  have hn (n : ℕ) : ‖iteratedFDeriv ℝ n tR y‖ =
      max (max ‖iteratedFDeriv ℝ n (fun _ : E => q) y‖
        (max ‖iteratedFDeriv ℝ n (fun z : E => z) y‖
          ‖iteratedFDeriv ℝ n R y‖))
        ‖iteratedFDeriv ℝ (n+1) R y‖ := by
    change ‖iteratedFDeriv ℝ n (fun z => ((q,(z,R z)),fderiv ℝ R z)) y‖ = _
    rw [iteratedFDeriv_prodMk hqy.contDiffAt hdR.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk contDiffAt_const (hid.prodMk hR).contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod,
      iteratedFDeriv_prodMk hid.contDiffAt hR.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod, norm_iteratedFDeriv_fderiv]
  have hc (n : ℕ) (hn : n ≠ 0) :
      iteratedFDeriv ℝ n (fun _ : E => q) y = 0 := by
    exact congrFun (iteratedFDeriv_const_of_ne hn q) y
  have hdi : fderiv ℝ (fun z : E => z) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext z
    exact fderiv_id
  have hi1 : ‖iteratedFDeriv ℝ 1 (fun z : E => z) y‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, hdi]
    exact ContinuousLinearMap.norm_id_le
  have hi2 : ‖iteratedFDeriv ℝ 2 (fun z : E => z) y‖ = 0 := by
    rw [← norm_iteratedFDeriv_fderiv, hdi]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
  have hR1 : ‖iteratedFDeriv ℝ 1 R y‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_one] using h1
  refine ⟨ht, ?_, ?_⟩
  · rw [hn 1, hc 1 (by decide), norm_zero]
    have h0 : 0 ≤ max 1 C2 := zero_le_one.trans (le_max_left _ _)
    exact max_le (max_le h0
      (max_le (hi1.trans (le_max_left _ _)) (hR1.trans (le_max_left _ _))))
      (h2.trans (le_max_right _ _))
  · rw [hn 2, hc 2 (by decide), norm_zero, hi2]
    have hC2 : 0 ≤ C2 := (norm_nonneg _).trans h2
    have hA : 0 ≤ max C2 C3 := hC2.trans (le_max_left _ _)
    have hAb : max C2 C3 ≤ max C2 C3 * beta :=
      le_mul_of_one_le_right hA hbeta
    have h0 : 0 ≤ max C2 C3 * beta := hA.trans hAb
    exact max_le (max_le h0 (max_le h0
      (h2.trans ((le_max_left _ _).trans hAb))))
      (h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hbeta)))

end OAI.AnisotropicCalderon
