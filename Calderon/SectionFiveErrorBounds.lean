import Calderon.SectionFiveErrorForms

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.SectionFiveErrorForms
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph BoundedSpectralMultiplier WeightedBaseSpectral

lemma norm_sq_le_sum {ι : Type*} [Fintype ι] (U : ι → SphereL2) (i : ι) :
    ‖U i‖^2 ≤ ∑ j, ‖U j‖^2 := by
  classical
  exact Finset.single_le_sum (f := fun j : ι => (‖U j‖ : ℝ)^2)
    (fun j _ => sq_nonneg (‖U j‖ : ℝ)) (Finset.mem_univ i)

lemma norm_mul_norm_le_sum {ι : Type*} [Fintype ι] (U : ι → SphereL2) (i j : ι) :
    ‖U i‖ * ‖U j‖ ≤ ∑ k, ‖U k‖^2 := by
  have hi := norm_sq_le_sum U i
  have hj := norm_sq_le_sum U j
  nlinarith [sq_nonneg (‖U i‖-‖U j‖)]

lemma weighted_gradient_square_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι] (beta : ℝ) (hbeta : 0 ≤ beta)
    (G0 : ι → SphereL2) (U1 : SphereL2) (Ghalf : ι → SphereL2) (Uthree : SphereL2) :
    beta⁻¹ * (∑ i, ‖Ghalf i‖^2) ≤ sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree := by
  have h := angular_error_terms_le_sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree
  have hz := mul_nonneg hbeta (sq_nonneg ‖Uthree‖)
  linarith

lemma weighted_value_square_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι] (beta : ℝ) (hbeta : 0 ≤ beta)
    (G0 : ι → SphereL2) (U1 : SphereL2) (Ghalf : ι → SphereL2) (Uthree : SphereL2) :
    beta * ‖Uthree‖^2 ≤ sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree := by
  have h := angular_error_terms_le_sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree
  have hz : 0 ≤ beta⁻¹ * (∑ i, ‖Ghalf i‖^2) := by positivity
  linarith

theorem abs_principal_spectral_form_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C : ℝ) (hbeta : 0 < beta) (hC : 0 ≤ C)
    (w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ C * besselWeight 1 k)
    (G0 Ghalf : ι → SphereL2) (U1 Uthree a : SphereL2) (i j : ι)
    (ha : (G0 i,a) ∈ spectralGraph hO hD w)
    (hhalf : ∀ k, (G0 k,Ghalf k) ∈ sphereBesselGraph hO hD (1/2)) :
    |beta⁻¹ * ⟪a,G0 j⟫_ℝ| ≤ C * sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree := by
  have hw' (k : ℕ) : |w k| ≤ C * (besselWeight (1/2) k * besselWeight (1/2) k) := by
    have hsum : (1/2 : ℝ)+(1/2)=1 := by norm_num
    rw [← besselWeight_add,hsum]
    exact hw k
  have hs := abs_inner_spectralGraph_le hO hD w (1/2) (1/2) C hC hw'
    (G0 i) a (Ghalf i) (G0 j) (Ghalf j) ha (hhalf i) (hhalf j)
  rw [abs_mul,abs_of_pos (inv_pos.mpr hbeta)]
  calc
    _ ≤ beta⁻¹ * (C * ‖Ghalf i‖ * ‖Ghalf j‖) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hbeta.le)
    _ = C * (beta⁻¹ * (‖Ghalf i‖ * ‖Ghalf j‖)) := by ring
    _ ≤ C * (beta⁻¹ * (∑ k, ‖Ghalf k‖^2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_mul_norm_le_sum Ghalf i j)
        (inv_nonneg.mpr hbeta.le)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_gradient_square_le_sourceNormSquareIntegrand beta hbeta.le G0 U1 Ghalf Uthree) hC

theorem abs_mixed_spectral_form_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C : ℝ) (hbeta : 0 < beta) (hC : 0 ≤ C)
    (w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ C * besselWeight 2 k)
    (G0 Ghalf : ι → SphereL2) (phi U1 Uthree a : SphereL2) (i : ι)
    (ha : (G0 i,a) ∈ spectralGraph hO hD w)
    (hhalf : (G0 i,Ghalf i) ∈ sphereBesselGraph hO hD (1/2))
    (hthree : (phi,Uthree) ∈ sphereBesselGraph hO hD (3/2)) :
    |⟪a,phi⟫_ℝ| ≤ C * sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree := by
  have hw' (k : ℕ) : |w k| ≤ C * (besselWeight (1/2) k * besselWeight (3/2) k) := by
    have hsum : (1/2 : ℝ)+(3/2)=2 := by norm_num
    rw [← besselWeight_add,hsum]
    exact hw k
  have hs := abs_inner_spectralGraph_le hO hD w (1/2) (3/2) C hC hw'
    (G0 i) a (Ghalf i) phi Uthree ha hhalf hthree
  calc
    _ ≤ C * (‖Ghalf i‖ * ‖Uthree‖) := by simpa only [mul_assoc] using hs
    _ ≤ C * (beta⁻¹ * ‖Ghalf i‖^2 + beta * ‖Uthree‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_weighted_sq beta _ _ hbeta) hC
    _ ≤ C * (beta⁻¹ * (∑ k, ‖Ghalf k‖^2) + beta * ‖Uthree‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (norm_sq_le_sum Ghalf i) (inv_nonneg.mpr hbeta.le)) le_rfl) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (angular_error_terms_le_sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree) hC

theorem abs_zero_spectral_form_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C : ℝ) (hbeta : 0 < beta) (hC : 0 ≤ C)
    (w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ C * besselWeight 3 k)
    (G0 Ghalf : ι → SphereL2) (phi U1 Uthree a : SphereL2)
    (ha : (phi,a) ∈ spectralGraph hO hD w)
    (hthree : (phi,Uthree) ∈ sphereBesselGraph hO hD (3/2)) :
    |beta * ⟪a,phi⟫_ℝ| ≤ C * sourceNormSquareIntegrand beta G0 U1 Ghalf Uthree := by
  have hw' (k : ℕ) : |w k| ≤ C * (besselWeight (3/2) k * besselWeight (3/2) k) := by
    have hsum : (3/2 : ℝ)+(3/2)=3 := by norm_num
    rw [← besselWeight_add,hsum]
    exact hw k
  have hs := abs_inner_spectralGraph_le hO hD w (3/2) (3/2) C hC hw'
    phi a Uthree phi Uthree ha hthree hthree
  rw [abs_mul,abs_of_pos hbeta]
  calc
    _ ≤ beta * (C * ‖Uthree‖ * ‖Uthree‖) := mul_le_mul_of_nonneg_left hs hbeta.le
    _ = C * (beta * ‖Uthree‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_value_square_le_sourceNormSquareIntegrand beta hbeta.le G0 U1 Ghalf Uthree) hC

/-- Actual base integration converts an established pointwise form bound into an N bound. -/
theorem abs_integral_form_le_sourceNormSquare {ι : Type*} [Fintype ι]
    (g : MatrixField) (L lam epsilon C : ℝ) (hepsilon : 0 ≤ epsilon)
    (beta : R3 → ℝ) (G0 Ghalf : R3 → ι → SphereL2)
    (U1 Uthree : R3 → SphereL2) (form : R3 → ℝ)
    (hN : Integrable (fun x => sourceNormSquareIntegrand (beta x) (G0 x) (U1 x)
      (Ghalf x) (Uthree x)) (referenceBaseMeasure g L lam))
    (hform : Integrable form (referenceBaseMeasure g L lam))
    (hbound : ∀ x, |form x| ≤ C * sourceNormSquareIntegrand (beta x) (G0 x) (U1 x)
      (Ghalf x) (Uthree x)) :
    |∫ x, epsilon * form x ∂referenceBaseMeasure g L lam| ≤
      epsilon * C * sourceNormSquare g L lam beta G0 U1 Ghalf Uthree := by
  have hpoint : ∀ᵐ x ∂referenceBaseMeasure g L lam, ‖epsilon * form x‖ ≤
      (epsilon * C) * sourceNormSquareIntegrand (beta x) (G0 x) (U1 x) (Ghalf x) (Uthree x) := by
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hepsilon]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x) hepsilon
  have hi := norm_integral_le_of_norm_le (hN.const_mul (epsilon*C)) hpoint
  simpa only [Real.norm_eq_abs,integral_const_mul,sourceNormSquare] using hi

/-- Common-constant absorption after, and only after, the component errors have been bounded. -/
theorem absorb_common_error_bound (N principal remainder c C epsilon : ℝ)
    (hN : 0 ≤ N) (hc : 0 < c) (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hsmall : epsilon * C ≤ c/2)
    (hpositive : c * N ≤ principal + remainder)
    (herror : |remainder| ≤ epsilon * C * N) :
    (c/2) * N ≤ principal := by
  have hr := le_abs_self remainder
  have hs := mul_le_mul_of_nonneg_right hsmall hN
  linarith

end OAI.AnisotropicCalderon.SectionFiveErrorForms
