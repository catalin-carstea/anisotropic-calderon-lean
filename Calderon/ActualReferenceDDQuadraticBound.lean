import Calderon.ActualReferenceDDSpectralTransport
import Calderon.ReferenceWeightedApproximation
import Calderon.ActualHorizontalNormBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceDDQuadraticBound
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SpectralWeightComparison AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier
  SmoothSphereFields SmoothAngularApplication SmoothAmbientAngularCasimir AmbientAngularShift
  SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising AmbientReferenceCovariantCore
  ActualReferenceParallelRaising ActualReferenceScaledRaisingTransport ActualReferenceModelTrace
  ActualReferenceDecomposition ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDGeometryBounds ActualReferenceDDCoefficientSmallness ActualReferenceDDSpectralTransport
  ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation SmoothSphereRotationProjection ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds MetricOperator ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile WeightedBaseSpectral
  SectionFiveErrorForms BaseDensityAdjoint ActualSupportLocalSecondForm ReferenceWeightedApproximation

/- The genuine native covariant DD trace minus its ordinary scalar principal part.
   This is a component bound. Full physical U/E/F/drift/J/defect remain separate. -/

lemma norm_bessel_half_le_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u uh uone : SphereL2)
    (hh : (u,uh) ∈ sphereBesselGraph hO hD (1/2))
    (hone : (u,uone) ∈ sphereBesselGraph hO hD 1) : ‖uh‖ ≤ ‖uone‖ := by
  have ht := norm_spectralGraph_output_le hO hD (besselWeight (1/2)) (besselWeight 1)
    1 (by norm_num) (fun k => by
      rw [abs_of_pos (besselWeight_pos (1/2) k),abs_of_pos (besselWeight_pos 1 k),one_mul]
      exact besselWeight_mono (1/2) 1 (by norm_num) k) u uh uone hh hone
  simpa only [one_mul] using ht

lemma norm_product_div_le_source_weights
    (beta a b : ℝ) (hbeta : 1 ≤ beta) :
    (a*b)/beta ≤ beta⁻¹*a^2+beta^2*b^2 := by
  have hp : 0 < beta := by linarith
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hb3 : 1 ≤ beta^2*beta := by
    simpa only [one_mul] using mul_le_mul hb2 hbeta (by norm_num : (0:ℝ)≤1) (sq_nonneg beta)
  apply (div_le_iff₀ hp).mpr
  calc
    a*b ≤ a^2+b^2 := by nlinarith [sq_nonneg (a-b)]
    _ ≤ a^2+(beta^2*beta)*b^2 := add_le_add le_rfl
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb3 (sq_nonneg b))
    _ = (beta⁻¹*a^2+beta^2*b^2)*beta := by field_simp [hp.ne']

lemma lower_angular_weights_le_sourceNormSquareIntegrand
    (beta : ℝ) (hbeta : 1 ≤ beta) (G0 : Fin 3 → SphereL2)
    (Uhalf Uone : SphereL2) (Ghalf : Fin 3 → SphereL2) (Uthree : SphereL2)
    (hhalf : ‖Uhalf‖ ≤ ‖Uone‖) :
    beta⁻¹*‖Uhalf‖^2+beta*‖Uthree‖^2 ≤ sourceNormSquareIntegrand beta G0 Uone Ghalf Uthree := by
  have hp : 0 < beta := by linarith
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hinv : beta⁻¹ ≤ beta^2 := ((inv_le_one₀ hp).mpr hbeta).trans hb2
  have hhsq : ‖Uhalf‖^2 ≤ ‖Uone‖^2 := by
    simpa only [pow_two] using mul_le_mul hhalf hhalf (norm_nonneg Uhalf) (norm_nonneg Uone)
  have hterm : beta⁻¹*‖Uhalf‖^2 ≤ beta^2*‖Uone‖^2 := by
    calc
      _ ≤ beta⁻¹*‖Uone‖^2 := mul_le_mul_of_nonneg_left hhsq (inv_nonneg.mpr hp.le)
      _ ≤ beta^2*‖Uone‖^2 := mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖Uone‖)
  have hg0 : 0 ≤ ∑ i : Fin 3, ‖G0 i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hgh : 0 ≤ beta⁻¹*(∑ i : Fin 3, ‖Ghalf i‖^2) :=
    mul_nonneg (inv_nonneg.mpr hp.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  unfold sourceNormSquareIntegrand
  linarith

theorem abs_inner_referenceWeightedFirstBaseTrace_le_coordinate_norm
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (beta Cfirst eps : ℝ) (hb : 1 ≤ beta) (hC : 0 ≤ Cfirst) (heps : 0 ≤ eps)
    (hcoeff : ∀ j, ‖referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x‖ ≤ Cfirst*eps/beta) :
    |⟪referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤
      (3*Cfirst)*eps*sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) := by
  let phiHalf := ambientBesselField hO hD (1/2) (by norm_num) G hG x
  let phiOne := ambientBesselField hO hD 1 (by norm_num) G hG x
  let phiThree := ambientBesselField hO hD (3/2) (by norm_num) G hG x
  let gradHalf := fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x
  let gradZero := fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x
  let NN := sourceNormSquareIntegrand beta gradZero phiOne gradHalf phiThree
  have hpos : 0 < beta := by linarith
  have hCE : 0 ≤ Cfirst*eps := mul_nonneg hC heps
  have hcoef0 : 0 ≤ Cfirst*eps/beta := div_nonneg hCE hpos.le
  have hhalf : ‖phiHalf‖ ≤ ‖phiOne‖ := norm_bessel_half_le_one hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
  have hterm (j : Fin 3) : |⟪referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x
      (gradHalf j),phiHalf⟫_ℝ| ≤ Cfirst*eps*NN := by
    have hinner := abs_real_inner_le_norm
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x (gradHalf j)) phiHalf
    have hnorm := (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x).le_opNorm (gradHalf j)
    have hn1 := mul_le_mul_of_nonneg_right hnorm (norm_nonneg phiHalf)
    have hn2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff j) (norm_nonneg (gradHalf j))) (norm_nonneg phiHalf)
    have hn3 := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hcoef0 (norm_nonneg (gradHalf j)))
    have hgsq := norm_sq_le_sum gradHalf j
    have hgrad := mul_le_mul_of_nonneg_left hgsq (inv_nonneg.mpr hpos.le)
    have hrest : beta⁻¹*‖gradHalf j‖^2+beta^2*‖phiOne‖^2 ≤ NN := by
      have hg0 : 0 ≤ ∑ i : Fin 3, ‖gradZero i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hg3 : 0 ≤ beta*‖phiThree‖^2 := mul_nonneg hpos.le (sq_nonneg _)
      dsimp [NN,sourceNormSquareIntegrand]
      linarith
    calc
      _ ≤ (Cfirst*eps/beta*‖gradHalf j‖)*‖phiHalf‖ := hinner.trans (hn1.trans hn2)
      _ ≤ (Cfirst*eps/beta*‖gradHalf j‖)*‖phiOne‖ := hn3
      _ = (Cfirst*eps)*((‖gradHalf j‖*‖phiOne‖)/beta) := by ring
      _ ≤ (Cfirst*eps)*(beta⁻¹*‖gradHalf j‖^2+beta^2*‖phiOne‖^2) :=
        mul_le_mul_of_nonneg_left (norm_product_div_le_source_weights beta _ _ hb) hCE
      _ ≤ Cfirst*eps*NN := mul_le_mul_of_nonneg_left hrest hCE
  rw [referenceWeightedFirstBaseTrace_inner_half_identity hO hD g hg L lam δ R p h G hG x]
  have ht := abs_sum_three_le (fun j => ⟪referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x
    (gradHalf j),phiHalf⟫_ℝ) (Cfirst*eps*NN) hterm
  convert ht using 1 <;> ring

theorem abs_inner_referenceWeightedZeroBaseTrace_le_coordinate_norm
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (beta Czero eps : ℝ) (hb : 1 ≤ beta) (hC : 0 ≤ Czero) (heps : 0 ≤ eps)
    (hcoeff : ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x‖ ≤ Czero*eps) :
    |⟪referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤
      Czero*eps*sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) := by
  let phiHalf := ambientBesselField hO hD (1/2) (by norm_num) G hG x
  let phiOne := ambientBesselField hO hD 1 (by norm_num) G hG x
  let phiThree := ambientBesselField hO hD (3/2) (by norm_num) G hG x
  let gradHalf := fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x
  let gradZero := fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x
  let NN := sourceNormSquareIntegrand beta gradZero phiOne gradHalf phiThree
  have hpos : 0 < beta := by linarith
  have hCE : 0 ≤ Czero*eps := mul_nonneg hC heps
  have hhalf : ‖phiHalf‖ ≤ ‖phiOne‖ := norm_bessel_half_le_one hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
  have hrest := lower_angular_weights_le_sourceNormSquareIntegrand beta hb gradZero phiHalf phiOne gradHalf phiThree hhalf
  rw [referenceWeightedZeroBaseTrace_inner_half_identity hO hD g hg L lam δ R p h G hG x]
  calc
    _ ≤ ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x phiThree‖*‖phiHalf‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x‖*‖phiThree‖)*‖phiHalf‖ :=
      mul_le_mul_of_nonneg_right
        ((referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x).le_opNorm phiThree) (norm_nonneg _)
    _ ≤ (Czero*eps*‖phiThree‖)*‖phiHalf‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (norm_nonneg _)
    _ = (Czero*eps)*(‖phiHalf‖*‖phiThree‖) := by ring
    _ ≤ (Czero*eps)*(beta⁻¹*‖phiHalf‖^2+beta*‖phiThree‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_weighted_sq beta _ _ hpos) hCE
    _ ≤ Czero*eps*NN := mul_le_mul_of_nonneg_left hrest hCE

def referenceWeightedDDPrincipalRemainder
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x -
    scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x

theorem referenceWeightedDDPrincipalRemainder_eq_first_add_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x =
      referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x +
      referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x := by
  unfold referenceWeightedDDPrincipalRemainder
  rw [referenceWeightedCovectorTrace_ordinary_decomposition hO hD g hg L lam δ R p hδ hR h G hG x]
  abel

lemma contDiff_referenceWeightedDDPrincipalRemainder
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG) := by
  have he : referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG =
      fun x => referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x +
        referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x :=
    funext (referenceWeightedDDPrincipalRemainder_eq_first_add_zero hO hD g hg L lam δ R p hδ hR h G hG)
  rw [he]
  exact (contDiff_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG).add
    (contDiff_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG)

lemma referenceWeightedDDPrincipalRemainder_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x = 0 := by
  rw [referenceWeightedDDPrincipalRemainder_eq_first_add_zero hO hD g hg L lam δ R p hδ hR h G hG x,
    referenceWeightedFirstBaseTrace_eq_zero_outside hO hD g hg L lam δ R p h G hG K hK hz x hx,
    referenceWeightedZeroBaseTrace_eq_zero_outside hO hD g hg L lam δ R p h G hG K hK hz x hx,zero_add]

lemma integrable_referenceWeightedDDPrincipalRemainder_density_pair
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 G hG)
    (contDiff_referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p hδ hR h hh G hG)
    (contDiff_ambientSphereL2 G hG) (hasCompactSupport_ambientSphereL2 G hG K hK hz)

theorem exists_referenceDD_remainder_pointwise_coordinate_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
    ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    ∀ x ∈ K, (∀ i j, |h x i j| ≤ eps*referenceRadius δ R p L x) →
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x
    1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
    ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
    |⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤
      C*eps*sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) := by
  obtain ⟨Cfirst,Czero,hFirst,hZero,hcoef⟩ := exists_referenceDD_normalized_coefficient_smallness hO hD g hg L hL K hK
  refine ⟨3*Cfirst+Czero,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h x hx hh beta hb hsmall G hG
  have hB := hcoef lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hb hsmall
  have hfirst := abs_inner_referenceWeightedFirstBaseTrace_le_coordinate_norm hO hD g hg L lam δ R p h G hG x beta Cfirst eps hb hFirst.le heps hB.1
  have hzero := abs_inner_referenceWeightedZeroBaseTrace_le_coordinate_norm hO hD g hg L lam δ R p h G hG x beta Czero eps hb hZero.le heps hB.2
  rw [referenceWeightedDDPrincipalRemainder_eq_first_add_zero hO hD g hg L lam δ R p hδ hR h G hG x,inner_add_left]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hzero).trans_eq (by ring))

theorem exists_referenceDD_remainder_coordinate_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
    ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    (∀ x ∈ K, ∀ i j, |h x i j| ≤ eps*referenceRadius δ R p L x) →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L lam δ R p x) →
    (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 ≤ eps) →
    ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
    (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
    |∫ x, referenceDensityFamily g L (lam,x)*
      ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤
      C*eps*sourceNormSquare g L lam (actualReferenceBeta g L lam δ R p)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
        (ambientBesselField hO hD 1 (by norm_num) G hG)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
        (ambientBesselField hO hD (3/2) (by norm_num) G hG) := by
  obtain ⟨C,hC,hpoint⟩ := exists_referenceDD_remainder_pointwise_coordinate_bound hO hD g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hj hb hsmall G hG hz
  let beta := actualReferenceBeta g L lam δ R p
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
  let FF : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*
    ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g hg L lam δ R p hL hδ hR
  have hi : Integrable FF := integrable_referenceWeightedDDPrincipalRemainder_density_pair
    hO hD g hg L lam δ R p hδ hR h hh G hG K hK hz
  have hN : Integrable (fun x => referenceDensityFamily g L (lam,x)*NN x) :=
    integrable_ambient_source_norm_on_compact hO hD g hg L lam beta hcont hpos G hG K hK hz
  have hbound (x : R3) : |FF x| ≤ (C*eps)*(referenceDensityFamily g L (lam,x)*NN x) := by
    by_cases hx : x ∈ K
    · have ht := hpoint lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h x hx (hj x hx) (hb x hx) (hsmall x hx) G hG
      change |referenceDensityFamily g L (lam,x)*
        ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤ _
      rw [abs_mul,abs_of_pos (referenceDensityFamily_pos g hg L (lam,x))]
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*(C*eps*NN x) :=
          mul_le_mul_of_nonneg_left ht (referenceDensityFamily_pos g hg L (lam,x)).le
        _ = _ := by ring
    · have hzphi := ambientSphereL2_eq_zero G hG x (hz x hx)
      have hNN : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      have hrho : 0 ≤ referenceDensityFamily g L (lam,x) := (referenceDensityFamily_pos g hg L (lam,x)).le
      change |referenceDensityFamily g L (lam,x)*
        ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤ _
      rw [hzphi,inner_zero_right,mul_zero,abs_zero]
      positivity
  have hiabs : Integrable (fun x => |FF x|) := by simpa only [Real.norm_eq_abs] using hi.norm
  have hint : |∫ x, FF x| ≤ (C*eps)*(∫ x, referenceDensityFamily g L (lam,x)*NN x) := by
    calc
      _ ≤ ∫ x, |FF x| := abs_integral_le_integral_abs
      _ ≤ ∫ x, (C*eps)*(referenceDensityFamily g L (lam,x)*NN x) :=
        integral_mono hiabs (hN.const_mul _) hbound
      _ = _ := integral_const_mul _ _
  rw [sourceNormSquare_eq_density_integral g hg L lam]
  exact hint

theorem exists_referenceDD_remainder_horizontal_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
    ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    (∀ x ∈ K, ∀ i j, |h x i j| ≤ eps*referenceRadius δ R p L x) →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L lam δ R p x) →
    (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 ≤ eps) →
    ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
    (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
    |∫ x, referenceDensityFamily g L (lam,x)*
      ⟪referenceWeightedDDPrincipalRemainder hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ| ≤
      C*eps*referenceHorizontalNormSquare hO hD g L lam
        (actualReferenceBeta g L lam δ R p) G hG := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceDD_remainder_coordinate_form_bound hO hD g hg L hL K hK
  obtain ⟨Ch,hCh,hcompare⟩ := exists_coordinate_horizontal_norm_comparison hO hD g hg L K hK
  refine ⟨C*Ch,mul_pos hC hCh,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hj hb hsmall G hG hz
  have ht := hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hj hb hsmall G hG hz
  have hcont := continuous_actualReferenceBeta g hg L lam δ R p hL hδ hR
  have hpos := actualReferenceBeta_pos g hg L lam δ R p hL hδ hR hp
  have hN := hcompare lam hlam (actualReferenceBeta g L lam δ R p) hcont hpos hb G hG hz
  have hm := mul_le_mul_of_nonneg_left hN.1 (mul_nonneg hC.le heps)
  exact ht.trans (hm.trans_eq (by ring))

end OAI.AnisotropicCalderon.ActualReferenceDDQuadraticBound
