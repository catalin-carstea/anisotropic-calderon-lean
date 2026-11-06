import Calderon.NativeFiniteHarmonicH1Bound
import Calderon.NativeHarmonicLiftFiniteCore
import Calderon.NativePolynomialRadialJets
import Calderon.SphereSobolevCompletion
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open NativePolynomialBulkMoments NativeFiniteHarmonicH1Bound NativeHarmonicLiftCompletion
  SphereHarmonic SmoothSphereRotationProjection SpectralWeightedGraph DirichletFamily EnergyBridge

def harmonicHalfBoundaryFiniteL : HarmonicFiniteCoefficients →ₗ[ℝ] SphereSobolev (1/2 : ℝ) :=
  DirectSum.toModule ℝ ℕ _ (fun k => (sphereSobolevSingleL (1/2 : ℝ) k).toLinearMap)

def harmonicFirstOrderFiniteL (hF : SphereFischerInner) :
    HarmonicFiniteCoefficients →ₗ[ℝ] BallH1 :=
  DirectSum.toModule ℝ ℕ _ (fun k =>
    ((TauCeti.Wkp.firstOrderL 0).toLinearMap.comp (polynomialBallSobolevLinearMap 1)).comp (harmonicPolynomialRepresentativeL hF k))

lemma harmonicHalfBoundaryFiniteL_eq_sum (a : HarmonicFiniteCoefficients) :
    harmonicHalfBoundaryFiniteL a =
      ∑ k ∈ a.support, sphereSobolevSingleL (1/2 : ℝ) k (a k) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact DirectSum.toModule_lof (R := ℝ)
    (φ := fun j => (sphereSobolevSingleL (1/2 : ℝ) j).toLinearMap) k (a k)

lemma harmonicFirstOrderFiniteL_eq_polynomial (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    harmonicFirstOrderFiniteL hF a = smoothSobolev (smoothPolynomialData
      (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k))) := by
  classical
  let P : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] BallH1 :=
    (TauCeti.Wkp.firstOrderL 0).toLinearMap.comp (polynomialBallSobolevLinearMap 1)
  have h : harmonicFirstOrderFiniteL hF a = ∑ k ∈ a.support,
      P (harmonicPolynomialRepresentativeL hF k (a k)) := by
    conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact DirectSum.toModule_lof (R := ℝ)
      (φ := fun j => P.comp (harmonicPolynomialRepresentativeL hF j)) k (a k)
  rw [h, ← map_sum]
  exact firstOrder_smoothBallSobolev 0
    (smoothPolynomialData (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)))

lemma besselWeight_one_half_sq (k : ℕ) :
    besselWeight (1/2 : ℝ) k ^ 2 = (1+(k:ℝ)) := by
  unfold besselWeight
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 1+(k:ℝ))]
  norm_num

lemma norm_sq_finite_boundary_sum (s : Finset ℕ) (a : ∀ k : ℕ, harmonicSphereSubspace k) :
    ‖∑ k ∈ s, sphereSobolevSingleL (1/2 : ℝ) k (a k)‖^2 =
      ∑ k ∈ s, (1+(k:ℝ))*‖a k‖^2 := by
  have hSingle (k : ℕ) : sphereSobolevSingleL (1/2 : ℝ) k (a k) =
      lp.single (E := fun j : ℕ => harmonicSphereSubspace j) 2 k
        (besselWeight (1/2 : ℝ) k • a k) := by
    change besselWeight (1/2 : ℝ) k • lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (a k) = _
    rw [lp.single_smul]
  simp_rw [hSingle]
  have h := lp.norm_sum_single (E := fun j : ℕ => harmonicSphereSubspace j)
    (p := 2) (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (fun k => besselWeight (1/2 : ℝ) k • a k) s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos (1/2 : ℝ) _),mul_pow,besselWeight_one_half_sq] using h

lemma norm_harmonicFirstOrderFiniteL_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    ‖harmonicFirstOrderFiniteL hF a‖ ≤ Real.sqrt sphereSurfaceMass * ‖harmonicHalfBoundaryFiniteL a‖ := by
  classical
  have h := (norm_sq_finite_harmonic_smoothSobolev_bounds hF hO a.support
    (fun k => harmonicPolynomialRepresentativeL hF k (a k))
    (fun k _ => harmonicPolynomialRepresentative_mem hF k (a k))).2
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative] at h
  change ‖smoothSobolev (smoothPolynomialData (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)))‖^2 ≤
    sphereSurfaceMass * ∑ k ∈ a.support, (1+(k:ℝ))*‖a k‖^2 at h
  rw [← harmonicFirstOrderFiniteL_eq_polynomial,← norm_sq_finite_boundary_sum,
    ← harmonicHalfBoundaryFiniteL_eq_sum] at h
  have hM : 0 ≤ sphereSurfaceMass := by
    unfold sphereSurfaceMass
    positivity
  have hs : (Real.sqrt sphereSurfaceMass*‖harmonicHalfBoundaryFiniteL a‖)^2 =
      sphereSurfaceMass*‖harmonicHalfBoundaryFiniteL a‖^2 := by
    rw [mul_pow,Real.sq_sqrt hM]
  have hp : 0 ≤ Real.sqrt sphereSurfaceMass*‖harmonicHalfBoundaryFiniteL a‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (harmonicFirstOrderFiniteL hF a)]

lemma denseRange_harmonicHalfBoundaryFiniteL : DenseRange harmonicHalfBoundaryFiniteL := by
  intro u
  have hmem (n : ℕ) : sphereSobolevPartialSum (1/2 : ℝ) n u ∈ Set.range harmonicHalfBoundaryFiniteL := by
    refine ⟨∑ k ∈ Finset.range n, DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
      (sphereSobolevCoefficientL (1/2 : ℝ) k u), ?_⟩
    simp only [map_sum,harmonicHalfBoundaryFiniteL,DirectSum.toModule_lof,sphereSobolevPartialSum,ContinuousLinearMap.coe_coe]
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum (1/2 : ℝ) u)
    (Filter.Eventually.of_forall fun n => subset_closure (hmem n))

def harmonicFirstOrderLiftCompletion (hF : SphereFischerInner) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
  LinearMap.extendOfNorm (E := HarmonicFiniteCoefficients)
    (Eₗ := SphereSobolev (1/2 : ℝ)) (F := BallH1)
    (harmonicFirstOrderFiniteL hF) harmonicHalfBoundaryFiniteL

lemma harmonicFirstOrderLiftCompletion_finite (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    harmonicFirstOrderLiftCompletion hF (harmonicHalfBoundaryFiniteL a) = harmonicFirstOrderFiniteL hF a := by
  unfold harmonicFirstOrderLiftCompletion
  have hd : DenseRange
      (harmonicHalfBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (1/2 : ℝ)) := by
    intro v
    have hmem (n : ℕ) : sphereSobolevPartialSum (1/2 : ℝ) n v ∈
        Set.range (harmonicHalfBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (1/2 : ℝ)) := by
      refine ⟨∑ k ∈ Finset.range n,
        DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
          (sphereSobolevCoefficientL (1/2 : ℝ) k v), ?_⟩
      simp only [map_sum,harmonicHalfBoundaryFiniteL,DirectSum.toModule_lof,
        sphereSobolevPartialSum,ContinuousLinearMap.coe_coe]
    exact isClosed_closure.mem_of_tendsto
      (tendsto_sphereSobolevPartialSum (1/2 : ℝ) v)
      (Filter.Eventually.of_forall fun n => subset_closure (hmem n))
  apply LinearMap.extendOfNorm_eq
  · exact hd
  · exact ⟨Real.sqrt sphereSurfaceMass, norm_harmonicFirstOrderFiniteL_le hF hO⟩

lemma norm_harmonicFirstOrderLiftCompletion_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (u : SphereSobolev (1/2 : ℝ)) :
    ‖harmonicFirstOrderLiftCompletion hF u‖ ≤ Real.sqrt sphereSurfaceMass*‖u‖ := by
  unfold harmonicFirstOrderLiftCompletion
  have hd : DenseRange
      (harmonicHalfBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (1/2 : ℝ)) := by
    intro v
    have hmem (n : ℕ) : sphereSobolevPartialSum (1/2 : ℝ) n v ∈
        Set.range (harmonicHalfBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (1/2 : ℝ)) := by
      refine ⟨∑ k ∈ Finset.range n,
        DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
          (sphereSobolevCoefficientL (1/2 : ℝ) k v), ?_⟩
      simp only [map_sum,harmonicHalfBoundaryFiniteL,DirectSum.toModule_lof,
        sphereSobolevPartialSum,ContinuousLinearMap.coe_coe]
    exact isClosed_closure.mem_of_tendsto
      (tendsto_sphereSobolevPartialSum (1/2 : ℝ) v)
      (Filter.Eventually.of_forall fun n => subset_closure (hmem n))
  apply LinearMap.norm_extendOfNorm_apply_le
  · exact hd
  · exact norm_harmonicFirstOrderFiniteL_le hF hO

#print axioms harmonicHalfBoundaryFiniteL
#print axioms harmonicFirstOrderFiniteL
#print axioms harmonicHalfBoundaryFiniteL_eq_sum
#print axioms harmonicFirstOrderFiniteL_eq_polynomial
#print axioms besselWeight_one_half_sq
#print axioms norm_sq_finite_boundary_sum
#print axioms norm_harmonicFirstOrderFiniteL_le
#print axioms denseRange_harmonicHalfBoundaryFiniteL
#print axioms harmonicFirstOrderLiftCompletion
#print axioms harmonicFirstOrderLiftCompletion_finite
#print axioms norm_harmonicFirstOrderLiftCompletion_le
end OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
