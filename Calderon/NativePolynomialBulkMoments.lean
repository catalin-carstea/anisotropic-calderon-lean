import Calderon.SphereHarmonicBridge
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open SphereHarmonic

def sphereSurfaceMass : ℝ := surfaceMeasure.real Set.univ

lemma sphereSurfaceMass_eq_three_ballVolume :
    sphereSurfaceMass = 3 * (volume : Measure R3).real (Metric.ball 0 1) := by
  simpa [sphereSurfaceMass, surfaceMeasure, R3] using
    (volume : Measure R3).toSphere_real_apply_univ

lemma surfaceMeasure_eq_mass_smul_probability :
    surfaceMeasure = (surfaceMeasure Set.univ) • sphereProbability := by
  unfold sphereProbability
  rw [smul_smul, ENNReal.mul_inv_cancel
    (Measure.measure_univ_ne_zero.mpr surfaceMeasure_ne_zero) (measure_ne_top _ _), one_smul]

lemma integral_surface_eq_mass_probability (a : UnitSphere → ℝ) :
    (∫ theta, a theta ∂surfaceMeasure) =
      sphereSurfaceMass * ∫ theta, a theta ∂sphereProbability := by
  rw [surfaceMeasure_eq_mass_smul_probability, integral_smul_measure]
  rfl

lemma integral_ball_eq_polar (f : R3 → ℝ) :
    (∫ x in Metric.ball (0 : R3) 1, f x) =
      ∫ z : UnitSphere × Set.Ioi (0 : ℝ),
        (Metric.ball (0 : R3) 1).indicator f (z.2.val • z.1.val)
        ∂surfaceMeasure.prod (Measure.volumeIoiPow 2) := by
  let F : R3 → ℝ := (Metric.ball (0 : R3) 1).indicator f
  let e := homeomorphUnitSphereProd R3
  have hmp := (volume : Measure R3).measurePreserving_homeomorphUnitSphereProd
  have he : Module.finrank ℝ R3 - 1 = 2 := by simp [R3]
  calc
    (∫ x in Metric.ball (0 : R3) 1, f x) = ∫ x, F x :=
      (integral_indicator measurableSet_ball).symm
    _ = ∫ x : ({(0 : R3)}ᶜ : Set R3), F x.val ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ z : UnitSphere × Set.Ioi (0 : ℝ), F (z.2.val • z.1.val)
        ∂surfaceMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := hmp.integral_comp (Homeomorph.measurableEmbedding _)
        (fun z => F (e.symm z).val)
      simpa only [e, Homeomorph.symm_apply_apply, he, surfaceMeasure,
        homeomorphUnitSphereProd_symm_apply_coe] using h
    _ = _ := rfl

lemma integral_radial_power_ball (n : ℕ) :
    (∫ r : Set.Ioi (0 : ℝ), if r.val < 1 then r.val^n else 0
      ∂Measure.volumeIoiPow 2) = 1 / ((n : ℝ)+3) := by
  let F : Set.Ioi (0 : ℝ) → ℝ := fun r => if r.val < 1 then r.val^n else 0
  have hm : Measurable (fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal (r.val^2)) := by
    fun_prop
  have ht : ∀ᵐ r : Set.Ioi (0 : ℝ) ∂(volume.comap Subtype.val),
      ENNReal.ofReal (r.val^2) < ∞ := Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc
    (∫ r : Set.Ioi (0 : ℝ), if r.val < 1 then r.val^n else 0
      ∂Measure.volumeIoiPow 2) =
        ∫ r : Set.Ioi (0 : ℝ), r.val^2 * F r ∂(volume.comap Subtype.val) := by
      rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul hm ht]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        simp only [ENNReal.toReal_ofReal (sq_nonneg r.val), smul_eq_mul, F])
    _ = ∫ x in Set.Ioi (0 : ℝ), x^2 * (if x<1 then x^n else 0) := by
      dsimp only [F]
      exact integral_subtype_comap measurableSet_Ioi
        (fun x : ℝ => x^2 * (if x<1 then x^n else 0))
    _ = ∫ x in Set.Ioi (0 : ℝ), (Set.Ioo (0 : ℝ) 1).indicator
          (fun x => x^(n+2)) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change x^2 * (if x<1 then x^n else 0) = (Set.Ioo (0 : ℝ) 1).indicator (fun x => x^(n+2)) x
      by_cases h : x<1
      · have hmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx,h⟩
        rw [if_pos h, Set.indicator_of_mem hmem, pow_add]
        ring
      · have hmem : x ∉ Set.Ioo (0 : ℝ) 1 := fun hx' => h hx'.2
        rw [if_neg h, Set.indicator_of_notMem hmem, mul_zero]
    _ = ∫ x in Set.Ioo (0 : ℝ) 1, x^(n+2) := by
      rw [integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self]
    _ = ∫ x in (0 : ℝ)..1, x^(n+2) := by
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
        intervalIntegral.integral_of_le zero_le_one]
    _ = 1 / ((n : ℝ)+3) := by
      rw [_root_.integral_pow]
      simp
      ring

lemma eval_homogeneous_smul {p : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) (r : ℝ) (x : R3) :
    p.eval (fun i => (r • x) i) = r^k * p.eval (fun i => x i) := by
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hd]
  ring

lemma integral_ball_of_homogeneous_scaling
    (f : R3 → ℝ) (a : UnitSphere → ℝ) (n : ℕ)
    (hscale : ∀ theta : UnitSphere, ∀ r : Set.Ioi (0 : ℝ),
      f (r.val • theta.val) = r.val^n * a theta) :
    (∫ x in Metric.ball (0 : R3) 1, f x) =
      sphereSurfaceMass / ((n : ℝ)+3) * ∫ theta, a theta ∂sphereProbability := by
  rw [integral_ball_eq_polar]
  have heq : (fun z : UnitSphere × Set.Ioi (0 : ℝ) =>
      (Metric.ball (0 : R3) 1).indicator f (z.2.val • z.1.val)) =
      (fun z : UnitSphere × Set.Ioi (0 : ℝ) =>
        a z.1 * (if z.2.val < 1 then z.2.val^n else 0)) := by
    funext z
    have hn : ‖z.2.val • z.1.val‖ = z.2.val := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.property,
        mem_sphere_zero_iff_norm.mp z.1.property, mul_one]
    by_cases hr : z.2.val < 1
    · rw [Set.indicator_of_mem (by simpa only [Metric.mem_ball, dist_zero_right, hn] using hr),
        hscale, if_pos hr]
      ring
    · rw [Set.indicator_of_notMem (by simpa only [Metric.mem_ball, dist_zero_right, hn] using hr),
        if_neg hr, mul_zero]
  rw [heq, integral_prod_mul (μ := surfaceMeasure) (ν := Measure.volumeIoiPow 2)
    a (fun r : Set.Ioi (0 : ℝ) => if r.val<1 then r.val^n else 0),
    integral_radial_power_ball, integral_surface_eq_mass_probability]
  ring

lemma integral_ball_polynomial_product {p q : MvPolynomial (Fin 3) ℝ} {k l : ℕ}
    (hp : p.IsHomogeneous k) (hq : q.IsHomogeneous l) :
    (∫ x in Metric.ball (0 : R3) 1,
      p.eval (fun i => x i) * q.eval (fun i => x i)) =
      sphereSurfaceMass / ((k : ℝ)+(l : ℝ)+3) *
        ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ := by
  rw [polynomialSphereL2_inner]
  convert integral_ball_of_homogeneous_scaling
    (fun x => p.eval (fun i => x i)*q.eval (fun i => x i))
    (fun theta => p.eval (fun i => theta.val i)*q.eval (fun i => theta.val i)) (k+l) ?_ using 1
  · simp only [Nat.cast_add]
  · intro theta r
    rw [eval_homogeneous_smul hp, eval_homogeneous_smul hq, pow_add]
    ring

lemma integral_ball_polynomial_square {p : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) :
    (∫ x in Metric.ball (0 : R3) 1, (p.eval (fun i => x i))^2) =
      sphereSurfaceMass / (2*(k : ℝ)+3) * ‖polynomialSphereL2 p‖^2 := by
  have h := integral_ball_polynomial_product hp hp
  simpa only [← pow_two, real_inner_self_eq_norm_sq, two_mul] using h

lemma integral_ball_harmonic_orthogonal (hO : OrthogonalSphereHarmonics)
    {p q : MvPolynomial (Fin 3) ℝ} {k l : ℕ}
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous l) (hkl : k ≠ l) :
    (∫ x in Metric.ball (0 : R3) 1,
      p.eval (fun i => x i) * q.eval (fun i => x i)) = 0 := by
  rw [integral_ball_polynomial_product hp.1 hq.1,
    hO k l hkl _ (polynomialSphereL2_mem k p hp) _ (polynomialSphereL2_mem l q hq), mul_zero]

#print axioms sphereSurfaceMass
#print axioms sphereSurfaceMass_eq_three_ballVolume
#print axioms surfaceMeasure_eq_mass_smul_probability
#print axioms integral_surface_eq_mass_probability
#print axioms integral_ball_eq_polar
#print axioms integral_radial_power_ball
#print axioms eval_homogeneous_smul
#print axioms integral_ball_of_homogeneous_scaling
#print axioms integral_ball_polynomial_product
#print axioms integral_ball_polynomial_square
#print axioms integral_ball_harmonic_orthogonal
end OAI.AnisotropicCalderon.NativePolynomialBulkMoments
