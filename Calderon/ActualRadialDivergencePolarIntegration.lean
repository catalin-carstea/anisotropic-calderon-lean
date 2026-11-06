import Calderon.ActualRadialTestIntegration
import Calderon.NativePolynomialBulkMoments

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.RadialTestIntegration
open SphereHarmonic

/-! Exact vector-field radial integration using volume and its native
surface measure. -/

/-- Classical Euclidean divergence in a fixed orthonormal basis. -/
def radialDivergence (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3)
    (x : R3) : ℝ := ∑ i : Fin 3, ⟪b i, fderiv ℝ V x (b i)⟫_ℝ

theorem integral_radialNormSq_divergence
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    (∫ x : R3, χ (‖x‖^2) * radialDivergence b V x) =
      -(∫ x : R3, (2 * deriv χ (‖x‖^2)) * ⟪x,V x⟫_ℝ) := by
  classical
  let φ : 𝓓((⊤ : Opens R3), ℝ) := radialNormSqTestFunction χ hχ R hR hχ0
  let u (i : Fin 3) (x : R3) : ℝ := ⟪b i,V x⟫_ℝ
  have hu (i : Fin 3) : ContDiff ℝ 1 (u i) :=
    (innerSL ℝ (b i)).contDiff.comp hV
  have hdu (i : Fin 3) (x : R3) :
      fderiv ℝ (u i) x (b i) = ⟪b i,fderiv ℝ V x (b i)⟫_ℝ := by
    have hd := (innerSL ℝ (b i)).hasFDerivAt.comp x
      (hV.differentiable (by norm_num) x).hasFDerivAt
    exact congrArg (fun T : R3 →L[ℝ] ℝ => T (b i)) hd.fderiv
  have hIleft (i : Fin 3) : Integrable (fun x : R3 =>
      (2 * deriv χ (‖x‖^2) * ⟪x,b i⟫_ℝ) * u i x) := by
    have hi := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      (μ := (volume : Measure R3))
      ((hu i).continuous.continuousOn.locallyIntegrableOn MeasurableSet.univ) φ (b i)
    simpa only [φ, lineDeriv_radialNormSqTestFunction, smul_eq_mul] using hi
  have hIright (i : Fin 3) : Integrable (fun x : R3 =>
      χ (‖x‖^2) * ⟪b i,fderiv ℝ V x (b i)⟫_ℝ) := by
    have hc : Continuous (fun x : R3 => ⟪b i,fderiv ℝ V x (b i)⟫_ℝ) :=
      (innerSL ℝ (b i)).continuous.comp
        ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    exact TauCeti.integrable_smul_of_locallyIntegrableOn
      (μ := (volume : Measure R3))
      (hc.continuousOn.locallyIntegrableOn MeasurableSet.univ) φ
  have hi (i : Fin 3) := integral_radialNormSqTestFunction_fderiv
    (μ := (volume : Measure R3)) χ hχ R hR hχ0 (u i) (hu i) (b i)
  simp_rw [hdu] at hi
  have hs := congrArg (fun f : Fin 3 → ℝ => ∑ i, f i) (funext hi)
  simp only [Finset.sum_neg_distrib] at hs
  rw [← integral_finsetSum Finset.univ (fun i _ => hIleft i),
    ← integral_finsetSum Finset.univ (fun i _ => hIright i)] at hs
  have hleft : (fun x : R3 => ∑ i : Fin 3,
      (2 * deriv χ (‖x‖^2) * ⟪x,b i⟫_ℝ) * u i x) =
      (fun x : R3 => (2 * deriv χ (‖x‖^2)) * ⟪x,V x⟫_ℝ) := by
    funext x
    simp only [u, mul_assoc, ← Finset.mul_sum, b.sum_inner_mul_inner]
  have hright : (fun x : R3 => ∑ i : Fin 3,
      χ (‖x‖^2) * ⟪b i,fderiv ℝ V x (b i)⟫_ℝ) =
      (fun x : R3 => χ (‖x‖^2) * radialDivergence b V x) := by
    funext x
    simp only [radialDivergence, Finset.mul_sum]
  rw [hleft, hright] at hs
  linarith

/-- Global polar change of variables with the existing native surface measure. -/
theorem integral_eq_sphere_radial_product (f : R3 → ℝ) :
    (∫ x : R3, f x) =
      ∫ z : UnitSphere × Ioi (0 : ℝ), f (z.2.val • z.1.val)
        ∂surfaceMeasure.prod (Measure.volumeIoiPow 2) := by
  let e := homeomorphUnitSphereProd R3
  have hmp := (volume : Measure R3).measurePreserving_homeomorphUnitSphereProd
  have he : Module.finrank ℝ R3 - 1 = 2 := by simp [R3]
  calc
    (∫ x : R3, f x) =
        ∫ x : ({(0 : R3)}ᶜ : Set R3), f x.val ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := hmp.integral_comp (Homeomorph.measurableEmbedding _)
        (fun z => f (e.symm z).val)
      simpa only [e, Homeomorph.symm_apply_apply, he, surfaceMeasure,
        homeomorphUnitSphereProd_symm_apply_coe] using h

/-- Actual vector radial integration transported to the exact native sphere
and positive-radius product measure. No sphere-probability convention changes. -/
theorem integral_radialNormSq_divergence_eq_polar
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    (∫ z : UnitSphere × Ioi (0 : ℝ),
      χ (z.2.val^2) * radialDivergence b V (z.2.val • z.1.val)
        ∂surfaceMeasure.prod (Measure.volumeIoiPow 2)) =
      -(∫ z : UnitSphere × Ioi (0 : ℝ),
        (2 * deriv χ (z.2.val^2)) * z.2.val * ⟪z.1.val,V (z.2.val • z.1.val)⟫_ℝ
          ∂surfaceMeasure.prod (Measure.volumeIoiPow 2)) := by
  have hi := integral_radialNormSq_divergence b V hV χ hχ R hR hχ0
  rw [integral_eq_sphere_radial_product, integral_eq_sphere_radial_product] at hi
  have hn (z : UnitSphere × Ioi (0 : ℝ)) : ‖z.2.val • z.1.val‖ = z.2.val := by
    rw [norm_smul, norm_eq_of_mem_sphere z.1, mul_one,
      Real.norm_of_nonneg z.2.property.le]
  simp_rw [hn, real_inner_smul_left, mul_assoc] at hi ⊢
  exact hi

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.radialDivergence
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_radialNormSq_divergence
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_eq_sphere_radial_product
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_radialNormSq_divergence_eq_polar
