import Calderon.ActualRadialDivergencePolarIntegration
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.RadialTestIntegration
open SphereHarmonic

/-! Actual outer-radial integration of the vector divergence identity. -/

theorem integrable_sphere_radial_product (f : R3 → ℝ)
    (hf : Integrable f (volume : Measure R3)) :
    Integrable (fun z : UnitSphere × Ioi (0 : ℝ) => f (z.2.val • z.1.val))
      (surfaceMeasure.prod (Measure.volumeIoiPow 2)) := by
  let g : UnitSphere × Ioi (0 : ℝ) → ℝ := fun z => f (z.2.val • z.1.val)
  have hmp := (volume : Measure R3).measurePreserving_homeomorphUnitSphereProd
  have he : Module.finrank ℝ R3 - 1 = 2 := by simp [R3]
  have hg : g ∘ homeomorphUnitSphereProd R3 = f ∘ Subtype.val := by
    funext x
    have hx : ‖(x : R3)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp [g, smul_smul, hx]
  change Integrable g ((volume : Measure R3).toSphere.prod (Measure.volumeIoiPow 2))
  rw [← he, ← hmp.integrable_comp_emb (homeomorphUnitSphereProd R3).measurableEmbedding,
    hg, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
  exact hf.integrableOn

theorem integral_volumeIoiPow_two (h : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), h r.val ∂Measure.volumeIoiPow 2) =
      ∫ r in Ioi (0 : ℝ), r^2 * h r := by
  have hm : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val^2)) := by
    fun_prop
  have ht : ∀ᵐ r : Ioi (0 : ℝ) ∂(volume.comap Subtype.val),
      ENNReal.ofReal (r.val^2) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul hm ht]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  exact integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^2 * h r)

theorem integral_eq_integral_Ioi_surface (f : R3 → ℝ)
    (hf : Integrable f (volume : Measure R3)) :
    (∫ x : R3, f x) = ∫ r in Ioi (0 : ℝ), r^2 *
      ∫ «ω» : UnitSphere, f (r • «ω».val) ∂surfaceMeasure := by
  rw [integral_eq_sphere_radial_product,
    integral_prod_symm _ (integrable_sphere_radial_product f hf)]
  exact integral_volumeIoiPow_two
    (fun r : ℝ => ∫ «ω» : UnitSphere, f (r • «ω».val) ∂surfaceMeasure)

theorem integrable_radialNormSq_divergence
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    Integrable (fun x : R3 => χ (‖x‖^2) * radialDivergence b V x)
      (volume : Measure R3) := by
  have hc : Continuous (radialDivergence b V) := by
    unfold radialDivergence
    apply continuous_finset_sum
    intro i hi
    exact (innerSL ℝ (b i)).continuous.comp
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  exact TauCeti.integrable_smul_of_locallyIntegrableOn
    (μ := (volume : Measure R3))
    (hc.continuousOn.locallyIntegrableOn MeasurableSet.univ)
    (radialNormSqTestFunction χ hχ R hR hχ0)

theorem integrable_radialNormSq_flux
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    Integrable (fun x : R3 => (2 * deriv χ (‖x‖^2)) * ⟪x,V x⟫_ℝ)
      (volume : Measure R3) := by
  classical
  let φ : 𝓓((⊤ : Opens R3), ℝ) := radialNormSqTestFunction χ hχ R hR hχ0
  have hi (i : Fin 3) : Integrable (fun x : R3 =>
      (2 * deriv χ (‖x‖^2) * ⟪x,b i⟫_ℝ) * ⟪b i,V x⟫_ℝ)
      (volume : Measure R3) := by
    have hc : Continuous (fun x : R3 => ⟪b i,V x⟫_ℝ) :=
      (innerSL ℝ (b i)).continuous.comp hV.continuous
    have h := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      (μ := (volume : Measure R3))
      (hc.continuousOn.locallyIntegrableOn MeasurableSet.univ) φ (b i)
    simpa only [φ, lineDeriv_radialNormSqTestFunction, smul_eq_mul] using h
  have hs := integrable_finsetSum Finset.univ (fun i hi' => hi i)
  simpa only [mul_assoc, ← Finset.mul_sum, b.sum_inner_mul_inner] using hs

theorem integral_radialNormSq_divergence_surface
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    (∫ r in Ioi (0 : ℝ), r^2 * χ (r^2) *
      ∫ «ω» : UnitSphere, radialDivergence b V (r • «ω».val) ∂surfaceMeasure) =
      -(∫ r in Ioi (0 : ℝ), 2 * r^3 * deriv χ (r^2) *
        ∫ «ω» : UnitSphere, ⟪«ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure) := by
  have hd := integrable_radialNormSq_divergence b V hV χ hχ R hR hχ0
  have hf := integrable_radialNormSq_flux b V hV χ hχ R hR hχ0
  have hvol := integral_radialNormSq_divergence b V hV χ hχ R hR hχ0
  rw [integral_eq_integral_Ioi_surface _ hd, integral_eq_integral_Ioi_surface _ hf] at hvol
  have hn (r : ℝ) (hr : 0 < r) («ω» : UnitSphere) : ‖r • «ω».val‖ = r := by
    rw [norm_smul, norm_eq_of_mem_sphere «ω», mul_one, Real.norm_of_nonneg hr.le]
  have hleft : (∫ r in Ioi (0 : ℝ), r^2 *
      ∫ «ω» : UnitSphere, χ (‖r • «ω».val‖^2) * radialDivergence b V (r • «ω».val)
        ∂surfaceMeasure) =
      ∫ r in Ioi (0 : ℝ), r^2 * χ (r^2) *
        ∫ «ω» : UnitSphere, radialDivergence b V (r • «ω».val) ∂surfaceMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp_rw [hn r hr]
    rw [integral_const_mul, mul_assoc]
  have hright : (∫ r in Ioi (0 : ℝ), r^2 *
      ∫ «ω» : UnitSphere, (2 * deriv χ (‖r • «ω».val‖^2)) *
        ⟪r • «ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure) =
      ∫ r in Ioi (0 : ℝ), 2 * r^3 * deriv χ (r^2) *
        ∫ «ω» : UnitSphere, ⟪«ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp_rw [hn r hr, real_inner_smul_left, ← mul_assoc]
    rw [integral_const_mul]
    ring
  rw [hleft, hright] at hvol
  exact hvol

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integrable_sphere_radial_product
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_volumeIoiPow_two
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_eq_integral_Ioi_surface
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integrable_radialNormSq_divergence
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integrable_radialNormSq_flux
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_radialNormSq_divergence_surface
