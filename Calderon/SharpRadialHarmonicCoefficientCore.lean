import Calderon.NativeHarmonicLiftExtension
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal DirectSum
namespace OAI.AnisotropicCalderon.SphereHarmonic
open NativeHarmonicLiftCompletion SphereHilbertDecomposition SpectralWeightedGraph DirichletFamily

/-! Upfront expansion: EXPANSION-sharp-midpoint-coefficients-joint-v001.md. -/
lemma harmonicLiftCompletion_sphereSobolevSingle
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    harmonicLiftCompletion hF (sphereSobolevSingleL (3/2 : ℝ) k u) =
      polynomialBallSobolev 2 (harmonicPolynomialRepresentativeL hF k u) := by
  have h := harmonicLiftCompletion_finite hF hO
    (DirectSum.lof ℝ ℕ (fun j => ↥(harmonicSphereSubspace j)) k u)
  have hpolynomial : polynomialBallSobolevLinearMap 2 (harmonicPolynomialRepresentativeL hF k u) =
      polynomialBallSobolev 2 (harmonicPolynomialRepresentativeL hF k u) := rfl
  simpa only [harmonicBoundaryFiniteL,harmonicNativeFiniteL,DirectSum.toModule_lof,
    LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hpolynomial] using h

lemma sphereSobolevZeroEquiv_harmonic_subtype
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevZeroEquiv hO hD (u : SphereL2) = sphereSobolevSingleL 0 k u := by
  change sphereHarmonicDecomposition hO hD (u : SphereL2) =
    besselWeight 0 k • lp.single 2 k u
  rw [besselWeight_zero_order,one_smul]
  exact sphereHarmonicDecomposition_subtype hO hD k u

theorem sphereSobolev_clm_eq_of_single
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : ℝ) (A B : SphereSobolev s →L[ℝ] V)
    (h : ∀ k : ℕ, ∀ u : harmonicSphereSubspace k,
      A (sphereSobolevSingleL s k u) = B (sphereSobolevSingleL s k u)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  have hs (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    simp only [sphereSobolevPartialSum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact h k (sphereSobolevCoefficientL s k u)
  exact tendsto_nhds_unique
    (A.continuous.continuousAt.tendsto.comp (tendsto_sphereSobolevPartialSum s u))
    ((B.continuous.continuousAt.tendsto.comp (tendsto_sphereSobolevPartialSum s u)).congr
      (fun n => (hs n).symm))

end OAI.AnisotropicCalderon.SphereHarmonic
