import Calderon.ActualNormalizedSecondModelCoefficients
import Calderon.ActualAngularCommutatorHalfForm

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondMixedCommutatorForm
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ActualPhysicalMixedFirst NormalizedPrincipalMetric SmoothMetricFrame
  ActualAngularDerivativeRaisingCommutator ActualAngularCommutatorHalfForm
  ActualReferenceDDSpectralTransport PrincipalCommutator SectionFiveErrorForms ReferenceDensityBounds
  ActualHorizontalNormBridge

/-- Negative of the A/Astar coefficient in the second-base part of
[P,U]+2[V,T], restricted to the actual mixed-first summand. -/
def mixedSecondWordCoefficient (g1 g2 : MatrixField) (L lam : ℝ)
    (i j a b : Fin 3) (x : R3) : ℝ :=
  (2*referenceMetricGramFrame g1 L (lam,x) a i +
    physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i x) *
    physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b j x +
  2*physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i x *
    referenceMetricGramFrame g1 L (lam,x) b j

def mixedSecondWordNormalizedCoefficient
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, mixedSecondWordCoefficient g1 g2 L lam i j a b x •
    normalizedDerivativeRaisingCommutator hF hO hD a b

def mixedSecondHalfForm
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
      directionalFDeriv (coordinateDirection i) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x⟫_ℝ

lemma abs_mixedSecondWordCoefficient_le
    (g1 g2 : MatrixField) (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hh : ∀ i j, |referenceNormalizedPrincipalDifference g1 g2 L lam x i j| ≤ eps*radius)
    (hcoframe : ∀ i a, |referenceCoFrameEntry g1 L i a (lam,x)| ≤ M)
    (hframe : ∀ a i, |referenceMetricGramFrame g1 L (lam,x) a i| ≤ M)
    (i j a b : Fin 3) :
    |mixedSecondWordCoefficient g1 g2 L lam i j a b x| ≤
      24*M^2*eps*radius+36*M^2*eps^2*radius^2 := by
  let q : Fin 3 → Fin 3 → ℝ := fun a i => physicalMixedFirstCoefficient g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a i x
  have hq (a i : Fin 3) : |q a i| ≤ 6*M*eps*radius :=
    physicalMixedFirstCoefficient_bound g1 L lam _ x eps radius M heps hradius hM hh hcoframe a i
  have hp : 0 ≤ 6*M*eps*radius := by positivity
  have hlin : |2*referenceMetricGramFrame g1 L (lam,x) a i+q a i| ≤ 2*M+6*M*eps*radius := by
    calc
      _ ≤ |2*referenceMetricGramFrame g1 L (lam,x) a i|+|q a i| := abs_add_le _ _
      _ = 2*|referenceMetricGramFrame g1 L (lam,x) a i|+|q a i| := by
        rw [abs_mul]; norm_num
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hframe a i) (by norm_num)) (hq a i)
  change |(2*referenceMetricGramFrame g1 L (lam,x) a i+q a i)*q b j+
    2*q a i*referenceMetricGramFrame g1 L (lam,x) b j| ≤ _
  calc
    _ ≤ |(2*referenceMetricGramFrame g1 L (lam,x) a i+q a i)*q b j|+
        |2*q a i*referenceMetricGramFrame g1 L (lam,x) b j| := abs_add_le _ _
    _ = |2*referenceMetricGramFrame g1 L (lam,x) a i+q a i| *|q b j|+
        2*|q a i| *|referenceMetricGramFrame g1 L (lam,x) b j| := by
      simp only [abs_mul]; norm_num
    _ ≤ (2*M+6*M*eps*radius)*(6*M*eps*radius)+(2*(6*M*eps*radius))*M :=
      add_le_add (mul_le_mul hlin (hq b j) (abs_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left (hq a i) (by norm_num))
          (hframe b j) (abs_nonneg _) (by positivity))
    _ = _ := by ring

lemma norm_mixedSecondWordNormalizedCoefficient_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hh : ∀ i j, |referenceNormalizedPrincipalDifference g1 g2 L lam x i j| ≤ eps*radius)
    (hcoframe : ∀ i a, |referenceCoFrameEntry g1 L i a (lam,x)| ≤ M)
    (hframe : ∀ a i, |referenceMetricGramFrame g1 L (lam,x) a i| ≤ M) (i j : Fin 3) :
    ‖mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x‖ ≤
      135*(24*M^2*eps*radius+36*M^2*eps^2*radius^2) := by
  let E : ℝ := 24*M^2*eps*radius+36*M^2*eps^2*radius^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ht (a b : Fin 3) :
      ‖mixedSecondWordCoefficient g1 g2 L lam i j a b x •
        normalizedDerivativeRaisingCommutator hF hO hD a b‖ ≤ E*15 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul
      (abs_mixedSecondWordCoefficient_le g1 g2 L lam x eps radius M heps hradius hM hh hcoframe hframe i j a b)
      (norm_normalizedDerivativeRaisingCommutator_le hF hO hD a b) (norm_nonneg _) hE
  unfold mixedSecondWordNormalizedCoefficient
  calc
    _ ≤ ∑ a : Fin 3, ‖∑ b : Fin 3,
        mixedSecondWordCoefficient g1 g2 L lam i j a b x •
          normalizedDerivativeRaisingCommutator hF hO hD a b‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        ‖mixedSecondWordCoefficient g1 g2 L lam i j a b x •
          normalizedDerivativeRaisingCommutator hF hO hD a b‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, E*15 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ht a b))
    _ = _ := by simp only [Fin.sum_univ_three]; dsimp [E]; ring

theorem mixedSecondWord_inner_half_identity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) (i j : Fin 3) :
    ⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x),
      directionalFDeriv (coordinateDirection i) (ambientSphereL2 G hG) x⟫_ℝ =
    ⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
      directionalFDeriv (coordinateDirection i) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x⟫_ℝ := by
  have hc : PreservesSphereSpectralGraphs hO hD
      (mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x) := by
    unfold mixedSecondWordNormalizedCoefficient
    apply preservesSphereSpectralGraphs_sum
    intro a
    apply preservesSphereSpectralGraphs_sum
    intro b
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hF hO hD a b)
  have hj :
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x,
        directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) ∈
          SpectralWeightedGraph.sphereBesselGraph hO hD (1/2) := by
    convert directional_ambientBesselField_between_graph hO hD (1/2) 1
      (by norm_num) (by norm_num) G hG x (coordinateDirection j) using 1 <;> norm_num
  have hi :
      (directionalFDeriv (coordinateDirection i) (ambientSphereL2 G hG) x,
        directionalFDeriv (coordinateDirection i) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x) ∈
          SpectralWeightedGraph.sphereBesselGraph hO hD (1/2) :=
    directionalDeriv_besselGraph hO hD (1/2) (coordinateDirection i) _ _
      (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG)
      (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG) x
  exact SpectralWeightedGraph.spectralGraph_inner_symm hO hD (SpectralWeightedGraph.besselWeight (1/2))
    _ _ _ _ (hc _ _ _ hj) hi

theorem abs_mixedSecondHalfForm_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hh : ∀ i j, |referenceNormalizedPrincipalDifference g1 g2 L lam x i j| ≤ eps*radius)
    (hcoframe : ∀ i a, |referenceCoFrameEntry g1 L i a (lam,x)| ≤ M)
    (hframe : ∀ a i, |referenceMetricGramFrame g1 L (lam,x) a i| ≤ M)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    |mixedSecondHalfForm hF hO hD g1 g2 L lam G hG x| ≤
      405*(24*M^2*eps*radius+36*M^2*eps^2*radius^2) *
        (∑ j : Fin 3, ‖directionalFDeriv (coordinateDirection j)
          (ambientBesselField hO hD (1/2) (by norm_num) G hG) x‖^2) := by
  let v : Fin 3 → SphereL2 := fun j => directionalFDeriv (coordinateDirection j)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG) x
  let C : ℝ := 135*(24*M^2*eps*radius+36*M^2*eps^2*radius^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht (i j : Fin 3) :
      |⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x (v j),v i⟫_ℝ| ≤
        C*‖v j‖*‖v i‖ := by
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x).le_of_opNorm_le
        (norm_mixedSecondWordNormalizedCoefficient_le hF hO hD g1 g2 L lam x eps radius M
          heps hradius hM hh hcoframe hframe i j) (v j)) (norm_nonneg _))
  have hSq : (∑ j : Fin 3, ‖v j‖)^2 ≤ 3*(∑ j : Fin 3, ‖v j‖^2) := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),sq_nonneg (‖v 1‖-‖v 2‖)]
  change |∑ i : Fin 3, ∑ j : Fin 3,
    ⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x (v j),v i⟫_ℝ| ≤ _
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3,
        ⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x (v j),v i⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        |⟪mixedSecondWordNormalizedCoefficient hF hO hD g1 g2 L lam i j x (v j),v i⟫_ℝ| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, C*‖v j‖*‖v i‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = C*(∑ j : Fin 3, ‖v j‖)^2 := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ C*(3*(∑ j : Fin 3, ‖v j‖^2)) := mul_le_mul_of_nonneg_left hSq hC
    _ = _ := by dsimp [C,v]; ring

theorem abs_mixedSecondHalfForm_le_coordinate_integrand
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (x : R3) (eps radius M beta D : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hbeta : 0 < beta)
    (hDnonneg : 0 ≤ D) (hsmall : eps*radius ≤ 1) (hrb : radius*beta ≤ D)
    (hh : ∀ i j, |referenceNormalizedPrincipalDifference g1 g2 L lam x i j| ≤ eps*radius)
    (hcoframe : ∀ i a, |referenceCoFrameEntry g1 L i a (lam,x)| ≤ M)
    (hframe : ∀ a i, |referenceMetricGramFrame g1 L (lam,x) a i| ≤ M)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    |mixedSecondHalfForm hF hO hD g1 g2 L lam G hG x| ≤
      24300*M^2*eps*D * sourceNormSquareIntegrand beta
        (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
        (ambientBesselField hO hD 1 (by norm_num) G hG x)
        (fun j => directionalFDeriv (coordinateDirection j)
          (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
        (ambientBesselField hO hD (3/2) (by norm_num) G hG x) := by
  let S : ℝ := ∑ j : Fin 3, ‖directionalFDeriv (coordinateDirection j)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG) x‖^2
  let NC : ℝ := sourceNormSquareIntegrand beta
    (fun j : Fin 3 => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (fun j : Fin 3 => directionalFDeriv (coordinateDirection j)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hNC : 0 ≤ NC := by dsimp [NC,sourceNormSquareIntegrand]; positivity
  have hsummand : beta⁻¹*S ≤ NC := by
    have h0 : 0 ≤ ∑ j : Fin 3, ‖directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h1 : 0 ≤ beta^2*‖ambientBesselField hO hD 1 (by norm_num) G hG x‖^2 := by positivity
    have h3 : 0 ≤ beta*‖ambientBesselField hO hD (3/2) (by norm_num) G hG x‖^2 := by positivity
    dsimp only [NC,sourceNormSquareIntegrand]
    change beta⁻¹*S ≤ _
    linarith
  have hScaled : S ≤ beta*NC := by
    have h := mul_le_mul_of_nonneg_left hsummand hbeta.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hbeta.ne',one_mul] using h
  have ht : (eps*radius)^2 ≤ eps*radius := by
    nlinarith [mul_nonneg heps hradius]
  have hCoeff : 405*(24*M^2*eps*radius+36*M^2*eps^2*radius^2) ≤
      24300*M^2*eps*radius := by
    have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 36*M^2)
    nlinarith only [h]
  change |mixedSecondHalfForm hF hO hD g1 g2 L lam G hG x| ≤ 24300*M^2*eps*D*NC
  calc
    _ ≤ 405*(24*M^2*eps*radius+36*M^2*eps^2*radius^2)*S :=
      abs_mixedSecondHalfForm_le hF hO hD g1 g2 L lam x eps radius M heps hradius hM hh hcoframe hframe G hG
    _ ≤ (24300*M^2*eps*radius)*S := mul_le_mul_of_nonneg_right hCoeff hS
    _ ≤ (24300*M^2*eps*radius)*(beta*NC) := mul_le_mul_of_nonneg_left hScaled (by positivity)
    _ = (24300*M^2*eps)*(radius*beta)*NC := by ring
    _ ≤ (24300*M^2*eps)*D*NC := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrb (by positivity)) hNC
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualNormalizedSecondMixedCommutatorForm
