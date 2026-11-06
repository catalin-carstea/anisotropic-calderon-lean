import Calderon.NativeFiniteHarmonicH3Bound
import Calderon.NativeHarmonicLiftFiniteCore

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
open NativePolynomialBulkMoments NativeFiniteHarmonicH3Bound NativeHarmonicLiftCompletion
  SphereHarmonic SmoothSphereRotationProjection SpectralWeightedGraph DirichletFamily

def harmonicBoundaryFiniteL : HarmonicFiniteCoefficients →ₗ[ℝ] SphereSobolev (5/2 : ℝ) :=
  DirectSum.toModule ℝ ℕ _ (fun k => (sphereSobolevSingleL (5/2 : ℝ) k).toLinearMap)

def harmonicNativeFiniteL (hF : SphereFischerInner) :
    HarmonicFiniteCoefficients →ₗ[ℝ] BallSobolev 3 :=
  DirectSum.toModule ℝ ℕ _ (fun k =>
    (polynomialBallSobolevLinearMap 3).comp (harmonicPolynomialRepresentativeL hF k))

lemma harmonicBoundaryFiniteL_eq_sum (a : HarmonicFiniteCoefficients) :
    harmonicBoundaryFiniteL a =
      ∑ k ∈ a.support, sphereSobolevSingleL (5/2 : ℝ) k (a k) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact DirectSum.toModule_lof (R := ℝ)
    (φ := fun j => (sphereSobolevSingleL (5/2 : ℝ) j).toLinearMap) k (a k)

lemma harmonicNativeFiniteL_eq_polynomial (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    harmonicNativeFiniteL hF a = polynomialBallSobolev 3
      (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)) := by
  classical
  have h : harmonicNativeFiniteL hF a = ∑ k ∈ a.support,
      polynomialBallSobolevLinearMap 3 (harmonicPolynomialRepresentativeL hF k (a k)) := by
    conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact DirectSum.toModule_lof (R := ℝ)
      (φ := fun j => (polynomialBallSobolevLinearMap 3).comp
        (harmonicPolynomialRepresentativeL hF j)) k (a k)
  rw [h, ← map_sum]
  rfl

lemma besselWeight_five_halves_sq (k : ℕ) :
    besselWeight (5/2 : ℝ) k ^ 2 = (1+(k:ℝ))^5 := by
  unfold besselWeight
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 1+(k:ℝ))]
  norm_num

lemma norm_sq_finite_boundary_sum (s : Finset ℕ) (a : ∀ k : ℕ, harmonicSphereSubspace k) :
    ‖∑ k ∈ s, sphereSobolevSingleL (5/2 : ℝ) k (a k)‖^2 =
      ∑ k ∈ s, (1+(k:ℝ))^5*‖a k‖^2 := by
  have hSingle (k : ℕ) : sphereSobolevSingleL (5/2 : ℝ) k (a k) =
      lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 k
        (besselWeight (5/2 : ℝ) k • a k) := by
    change besselWeight (5/2 : ℝ) k • lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (a k) = _
    rw [lp.single_smul]
  simp_rw [hSingle]
  have h := lp.norm_sum_single (E := fun j : ℕ => harmonicSphereSubspace j)
    (p := 2) (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (fun k => besselWeight (5/2 : ℝ) k • a k) s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos (5/2 : ℝ) _),mul_pow,besselWeight_five_halves_sq] using h

lemma norm_harmonicNativeFiniteL_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    ‖harmonicNativeFiniteL hF a‖ ≤ Real.sqrt (64*sphereSurfaceMass) * ‖harmonicBoundaryFiniteL a‖ := by
  classical
  have h := norm_sq_finite_harmonic_polynomialBallSobolev_three_le hF hO a.support
    (fun k => harmonicPolynomialRepresentativeL hF k (a k))
    (fun k _ => harmonicPolynomialRepresentative_mem hF k (a k))
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative] at h
  change ‖polynomialBallSobolev 3 (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k))‖^2 ≤
    64*sphereSurfaceMass * ∑ k ∈ a.support, (1+(k:ℝ))^5*‖a k‖^2 at h
  rw [← harmonicNativeFiniteL_eq_polynomial,← norm_sq_finite_boundary_sum,
    ← harmonicBoundaryFiniteL_eq_sum] at h
  have hM : 0 ≤ 64*sphereSurfaceMass := by
    unfold sphereSurfaceMass
    positivity
  have hs : (Real.sqrt (64*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖)^2 =
      (64*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖^2 := by
    rw [mul_pow,Real.sq_sqrt hM]
  have hp : 0 ≤ Real.sqrt (64*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (harmonicNativeFiniteL hF a)]

lemma denseRange_harmonicBoundaryFiniteL : DenseRange harmonicBoundaryFiniteL := by
  intro u
  have hmem (n : ℕ) : sphereSobolevPartialSum (5/2 : ℝ) n u ∈ Set.range harmonicBoundaryFiniteL := by
    refine ⟨∑ k ∈ Finset.range n, DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
      (sphereSobolevCoefficientL (5/2 : ℝ) k u), ?_⟩
    simp only [map_sum,harmonicBoundaryFiniteL,DirectSum.toModule_lof,sphereSobolevPartialSum, ContinuousLinearMap.coe_coe]
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum (5/2 : ℝ) u)
    (Filter.Eventually.of_forall fun n => subset_closure (hmem n))


end OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
