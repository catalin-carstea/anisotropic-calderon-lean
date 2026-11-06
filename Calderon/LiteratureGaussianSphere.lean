import Calderon.SphereHarmonicBridge
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian integrals of homogeneous functions in polar coordinates (helper for tasks 01, 03). -/

noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.SphereHarmonic

open Set in
/-- Radial Gaussian moment against `r ^ 2 dr` on `(0, ∞)`. -/
lemma radial_gamma (d : ℕ) :
    ∫ r : Ioi (0:ℝ), r.1 ^ d * Real.exp (-r.1 ^ 2) ∂(Measure.volumeIoiPow 2) =
      Real.Gamma ((d + 3) / 2) / 2 := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (measurable_subtype_coe.pow_const _).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ ↦ Real.toNNReal (a ^ 2) • (a ^ d * Real.exp (-a ^ 2)))]
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (d:ℝ) + 2) two_pos
    (by have := (Nat.cast_nonneg d : (0:ℝ) ≤ d); linarith)
  rw [show ((d:ℝ) + 2 + 1) / 2 = (d + 3) / 2 by ring] at h
  rw [div_eq_inv_mul, ← one_div, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx : (0:ℝ) < x := hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul,
    Real.rpow_add hx, Real.rpow_natCast, Real.rpow_two]
  ring

/-- For a continuous function homogeneous of degree `d`,
`∫_{ℝ³} f(x) e^{-|x|²} dx = (∫_{S²} f dσ) · Γ((d+3)/2) / 2`, where `σ` is `surfaceMeasure`. -/
theorem integral_mul_gaussian_of_homogeneous {f : R3 → ℝ} (hf : Continuous f) (d : ℕ)
    (hhom : ∀ (t : ℝ) (x : R3), 0 < t → f (t • x) = t ^ d * f x) :
    ∫ x : R3, f x * Real.exp (-‖x‖ ^ 2) =
      (∫ ω : UnitSphere, f ω ∂surfaceMeasure) * (Real.Gamma ((d + 3) / 2) / 2) := by
  set g : R3 → ℝ := fun x ↦ f x * Real.exp (-‖x‖ ^ 2) with hg
  have hdim : Module.finrank ℝ R3 - 1 = 2 := by simp
  have mp := (volume : Measure R3).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at mp
  calc ∫ x : R3, g x
      = ∫ x : ({(0:R3)}ᶜ : Set R3), g x.1 ∂((volume : Measure R3).comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl g,
          restrict_compl_singleton]
    _ = ∫ p : UnitSphere × Set.Ioi (0:ℝ),
          g ((homeomorphUnitSphereProd R3).symm p).1
          ∂(surfaceMeasure.prod (Measure.volumeIoiPow 2)) := by
        have := mp.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p ↦ g ((homeomorphUnitSphereProd R3).symm p).1)
        simp only [Homeomorph.symm_apply_apply] at this
        exact this
    _ = ∫ p : UnitSphere × Set.Ioi (0:ℝ), f p.1 * (p.2.1 ^ d * Real.exp (-p.2.1 ^ 2))
          ∂(surfaceMeasure.prod (Measure.volumeIoiPow 2)) := by
        congr 1; ext ⟨ω, r⟩
        simp only [hg, homeomorphUnitSphereProd_symm_apply_coe]
        rw [hhom _ _ r.2, norm_smul, Real.norm_eq_abs, abs_of_pos r.2,
          norm_eq_of_mem_sphere ω, mul_one]
        ring
    _ = _ := by rw [integral_prod_mul (fun ω : UnitSphere ↦ f ω)
          (fun r : Set.Ioi (0:ℝ) ↦ r.1 ^ d * Real.exp (-r.1 ^ 2)), radial_gamma]

end OAI.AnisotropicCalderon.SphereHarmonic
