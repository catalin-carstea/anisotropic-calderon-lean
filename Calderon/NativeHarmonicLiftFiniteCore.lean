import Calderon.DenseRealLinearExtension
import Calderon.NativeFiniteHarmonicH2Bound
import Calderon.NativePolynomialRadialJets
import Calderon.SphereSobolevCompletion
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open NativePolynomialBulkMoments NativeFiniteHarmonicH2Bound
  SphereHarmonic SmoothSphereRotationProjection SpectralWeightedGraph DirichletFamily

abbrev HarmonicFiniteCoefficients := DirectSum ℕ (fun k => ↥(harmonicSphereSubspace k))

def harmonicPolynomialEquiv (hF : SphereFischerInner) (k : ℕ) :
    harmonicHomogeneous k ≃ₗ[ℝ] harmonicSphereSubspace k :=
  LinearEquiv.ofBijective (harmonicPolynomialSphereMap k) ⟨by
    intro p q h
    apply Subtype.ext
    exact (polynomialSphereL2_injective_degree hF k p q p.property q.property).mp
      (congrArg Subtype.val h), harmonicPolynomialSphereMap_surjective k⟩

def harmonicPolynomialRepresentativeL (hF : SphereFischerInner) (k : ℕ) :
    harmonicSphereSubspace k →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  (harmonicHomogeneous k).subtype.comp (harmonicPolynomialEquiv hF k).symm.toLinearMap

lemma harmonicPolynomialRepresentative_mem (hF : SphereFischerInner) (k : ℕ)
    (a : harmonicSphereSubspace k) :
    harmonicPolynomialRepresentativeL hF k a ∈ harmonicHomogeneous k :=
  ((harmonicPolynomialEquiv hF k).symm a).property

lemma polynomialSphereL2_harmonicPolynomialRepresentative (hF : SphereFischerInner) (k : ℕ)
    (a : harmonicSphereSubspace k) :
    polynomialSphereL2 (harmonicPolynomialRepresentativeL hF k a) = a.val := by
  have h := congrArg Subtype.val ((harmonicPolynomialEquiv hF k).apply_symm_apply a)
  exact h

def harmonicBoundaryFiniteL : HarmonicFiniteCoefficients →ₗ[ℝ] SphereSobolev (3/2 : ℝ) :=
  DirectSum.toModule ℝ ℕ _ (fun k => (sphereSobolevSingleL (3/2 : ℝ) k).toLinearMap)

def harmonicNativeFiniteL (hF : SphereFischerInner) :
    HarmonicFiniteCoefficients →ₗ[ℝ] BallSobolev 2 :=
  DirectSum.toModule ℝ ℕ _ (fun k =>
    (polynomialBallSobolevLinearMap 2).comp (harmonicPolynomialRepresentativeL hF k))

lemma harmonicBoundaryFiniteL_eq_sum (a : HarmonicFiniteCoefficients) :
    harmonicBoundaryFiniteL a =
      ∑ k ∈ a.support, sphereSobolevSingleL (3/2 : ℝ) k (a k) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact DirectSum.toModule_lof (R := ℝ)
    (φ := fun j => (sphereSobolevSingleL (3/2 : ℝ) j).toLinearMap) k (a k)

lemma harmonicNativeFiniteL_eq_polynomial (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    harmonicNativeFiniteL hF a = polynomialBallSobolev 2
      (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)) := by
  classical
  have h : harmonicNativeFiniteL hF a = ∑ k ∈ a.support,
      polynomialBallSobolevLinearMap 2 (harmonicPolynomialRepresentativeL hF k (a k)) := by
    conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact DirectSum.toModule_lof (R := ℝ)
      (φ := fun j => (polynomialBallSobolevLinearMap 2).comp
        (harmonicPolynomialRepresentativeL hF j)) k (a k)
  rw [h, ← map_sum]
  rfl

lemma besselWeight_three_halves_sq (k : ℕ) :
    besselWeight (3/2 : ℝ) k ^ 2 = (1+(k:ℝ))^3 := by
  unfold besselWeight
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 1+(k:ℝ))]
  norm_num

lemma norm_sq_finite_boundary_sum (s : Finset ℕ) (a : ∀ k : ℕ, harmonicSphereSubspace k) :
    ‖∑ k ∈ s, sphereSobolevSingleL (3/2 : ℝ) k (a k)‖^2 =
      ∑ k ∈ s, (1+(k:ℝ))^3*‖a k‖^2 := by
  have hSingle (k : ℕ) : sphereSobolevSingleL (3/2 : ℝ) k (a k) =
      lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 k
        (besselWeight (3/2 : ℝ) k • a k) := by
    change besselWeight (3/2 : ℝ) k • lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (a k) = _
    rw [lp.single_smul]
  simp_rw [hSingle]
  have h := lp.norm_sum_single (E := fun j : ℕ => harmonicSphereSubspace j)
    (p := 2) (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (fun k => besselWeight (3/2 : ℝ) k • a k) s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos (3/2 : ℝ) _),mul_pow,besselWeight_three_halves_sq] using h

lemma norm_harmonicNativeFiniteL_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    ‖harmonicNativeFiniteL hF a‖ ≤ Real.sqrt (3*sphereSurfaceMass) * ‖harmonicBoundaryFiniteL a‖ := by
  classical
  have h := norm_sq_finite_harmonic_polynomialBallSobolev_two_le hF hO a.support
    (fun k => harmonicPolynomialRepresentativeL hF k (a k))
    (fun k _ => harmonicPolynomialRepresentative_mem hF k (a k))
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative] at h
  change ‖polynomialBallSobolev 2 (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k))‖^2 ≤
    3*sphereSurfaceMass * ∑ k ∈ a.support, (1+(k:ℝ))^3*‖a k‖^2 at h
  rw [← harmonicNativeFiniteL_eq_polynomial,← norm_sq_finite_boundary_sum,
    ← harmonicBoundaryFiniteL_eq_sum] at h
  have hM : 0 ≤ 3*sphereSurfaceMass := by
    unfold sphereSurfaceMass
    positivity
  have hs : (Real.sqrt (3*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖)^2 =
      (3*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖^2 := by
    rw [mul_pow,Real.sq_sqrt hM]
  have hp : 0 ≤ Real.sqrt (3*sphereSurfaceMass)*‖harmonicBoundaryFiniteL a‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (harmonicNativeFiniteL hF a)]

lemma denseRange_harmonicBoundaryFiniteL : DenseRange harmonicBoundaryFiniteL := by
  intro u
  have hmem (n : ℕ) : sphereSobolevPartialSum (3/2 : ℝ) n u ∈ Set.range harmonicBoundaryFiniteL := by
    refine ⟨∑ k ∈ Finset.range n, DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
      (sphereSobolevCoefficientL (3/2 : ℝ) k u), ?_⟩
    simp only [map_sum,harmonicBoundaryFiniteL,DirectSum.toModule_lof,sphereSobolevPartialSum, ContinuousLinearMap.coe_coe]
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
    (Filter.Eventually.of_forall fun n => subset_closure (hmem n))

#print axioms harmonicPolynomialEquiv
#print axioms harmonicPolynomialRepresentativeL
#print axioms harmonicPolynomialRepresentative_mem
#print axioms polynomialSphereL2_harmonicPolynomialRepresentative
#print axioms harmonicBoundaryFiniteL
#print axioms harmonicNativeFiniteL
#print axioms harmonicBoundaryFiniteL_eq_sum
#print axioms harmonicNativeFiniteL_eq_polynomial
#print axioms besselWeight_three_halves_sq
#print axioms norm_sq_finite_boundary_sum
#print axioms norm_harmonicNativeFiniteL_le
#print axioms denseRange_harmonicBoundaryFiniteL
end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
