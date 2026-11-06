import Calderon.ActualMixedDensityRaisingCoefficientJets
import Calderon.ActualMixedSecondHorizontalFormBound
import Calderon.ActualScalarPrincipalAdjoint
import Calderon.ScalarHilbertFormBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator ActualPhysicalMixedFirst ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets CoordinateBootstrapJets ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityRaisingCoefficientJets ActualMixedDensityRemainderForm ActualMixedDensityRemainderProfile
  AmbientAngularShift BoundedAngularShift SpectralWeightedGraph SpectralWeightComparison SectionFiveErrorForms
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ConformalDepth RadiusProfile ReferenceWeightedApproximation

/-- Actual inverse-metric words are included with the same compact background
frame/coframe/density/inverse-density word budget; no free principal field is used. -/
def MixedPrincipalDensityBackgroundJetBound (g : MatrixField) (L lam : ℝ)
    (x : R3) (M : ℝ) (N : ℕ) : Prop :=
  MixedBackgroundCoordinateJetBound g L lam x M N ∧
    (∀ w : List (Fin 3), w.length ≤ N → ∀ i j : Fin 3,
      |coordinateFieldWordPartial w (fun y => referenceInverseEntryFamily g L i j (lam,y)) x| ≤ M)

/-- Concrete ordered E0 scalar/density word from -a_ij partial_i partial_j
of the W-density lowering coefficient, with literal a=rQ and native A_aG. -/
def mixedDensityScalarZeroField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  -(∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
    (referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j *
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
        (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a)) x) •
      ambientDerivativeField hF hO hD a G hG x)

def mixedDensityScalarZeroDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  referenceDensityFamily g1 L (lam,x) *
    ⟪mixedDensityScalarZeroField hF hO hD g1 g2 L lam δ R p G hG x,ambientSphereL2 G hG x⟫_ℝ

theorem exists_mixed_principal_density_background_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      MixedPrincipalDensityBackgroundJetBound g L lam x M N := by
  obtain ⟨MB,hMB,hB⟩ := exists_mixed_background_coordinate_jet_bound g hg L K hK N
  obtain ⟨MI,hMI,hI⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceInverseEntryFamily g L t.1 t.2)
    (fun t => contDiff_referenceInverseEntryFamily g hg L t.1 t.2) K hK N
  let M : ℝ := MB+MI
  have hBM : MB ≤ M := by dsimp [M]; linarith
  have hIM : MI ≤ M := by dsimp [M]; linarith
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro lam hlam x hx
  obtain ⟨hFrame,hCoFrame,hDensity,hInverseDensity⟩ := hB lam hlam x hx
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw a i
    exact (hFrame w hw a i).trans hBM
  · intro w hw u a
    exact (hCoFrame w hw u a).trans hBM
  · intro w hw
    exact (hDensity w hw).trans hBM
  · intro w hw
    exact (hInverseDensity w hw).trans hBM
  · intro w hw i j
    have h := (hI lam hlam x hx (i,j) w hw).trans hIM
    simpa only [Real.norm_eq_abs] using h

/-- Actual Q words are bounded by the genuine reference inverse plus actual h.
The source H8 convention and ordinary coordinate order are retained literally. -/
lemma abs_referenceNormalizedPrincipalMatrix_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N ≤ 8)
    (hM : 1 ≤ M) (hsmall : eps*radius ≤ 1)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M N)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i j : Fin 3) :
    |coordinateFieldWordPartial w (fun y => referenceNormalizedPrincipalMatrix g1 g2 L lam y i j) x| ≤ 2*M := by
  let inv : R3 → ℝ := fun y => referenceInverseEntryFamily g1 L i j (lam,y)
  let hh : R3 → ℝ := fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y i j
  have hi : ContDiff ℝ ∞ inv :=
    (contDiff_referenceInverseEntryFamily g1 hg1 L i j).comp (contDiff_const.prodMk contDiff_id)
  have hd : ContDiff ℝ ∞ hh := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j
  have hQ : (fun y => referenceNormalizedPrincipalMatrix g1 g2 L lam y i j) =
      fun y => inv y+hh y := by
    funext y
    dsimp [inv,hh]
    simp only [referenceNormalizedPrincipalDifference,normalizedPrincipalDifference,
      referenceNormalizedPrincipalMatrix,referenceInverseEntryFamily,Matrix.sub_apply]
    ring
  have hInv : |coordinateFieldWordPartial w inv x| ≤ M := hgeom.2 w hw i j
  have hDiff : |coordinateFieldWordPartial w hh x| ≤ eps*radius :=
    abs_actual_h_coordinateFieldWordPartial_le_of_H8 g1 g2 hg1 hg2 L lam x _ hH8 w (le_trans hw hN) i j
  rw [hQ,coordinateFieldWordPartial_add w inv hh hi hd]
  calc
    _ ≤ |coordinateFieldWordPartial w inv x|+|coordinateFieldWordPartial w hh x| := abs_add_le _ _
    _ ≤ M+eps*radius := add_le_add hInv hDiff
    _ ≤ 2*M := by linarith

theorem abs_mixedDensityScalarZeroDensity_le_coordinate_integrand
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) (eps M : ℝ) (beta : R3 → ℝ)
    (hδ : 0 < δ) (hR : 0 < R) (heps : 0 ≤ eps) (hM : 1 ≤ M)
    (hsmall : eps*referenceRadius δ R p L x ≤ 1) (hbeta : 1 ≤ beta x)
    (hgeom : MixedPrincipalDensityBackgroundJetBound g1 L lam x M 3)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    |mixedDensityScalarZeroDensity hF hO hD g1 g2 L lam δ R p G hG x| ≤
      497664*M^4*eps*(referenceRadius δ R p L x)^2 *
        (referenceDensityFamily g1 L (lam,x)*mixedCoordinateNormSquareIntegrand hO hD beta G hG x) := by
  let r : ℝ := referenceRadius δ R p L x
  let Q : Fin 3 → Fin 3 → ℝ := fun i j => referenceNormalizedPrincipalMatrix g1 g2 L lam x i j
  let d : Fin 3 → R3 → ℝ := fun a => physicalMixedDensityCorrection g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a
  let U : SphereL2 := ambientSphereL2 G hG x
  let U1 : SphereL2 := ambientBesselField hO hD 1 (by norm_num) G hG x
  let v0 : Fin 3 → SphereL2 := fun k => directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x
  let vh : Fin 3 → SphereL2 := fun k => directionalFDeriv (coordinateDirection k)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG) x
  let U3 : SphereL2 := ambientBesselField hO hD (3/2) (by norm_num) G hG x
  let NN : ℝ := mixedCoordinateNormSquareIntegrand hO hD beta G hG x
  let A : ℝ := 9216*M^4*eps*r^2
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMu := referenceDensityFamily_pos g1 hg1 L (lam,x)
  have hQ (i j : Fin 3) : |Q i j| ≤ 2*M := by
    have h := abs_referenceNormalizedPrincipalMatrix_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps r M 3 (by norm_num) hM hsmall hgeom hH8 [] (by simp) i j
    simpa only [coordinateFieldWordPartial,Q] using h
  have hdd (i j a : Fin 3) :
      |directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d a)) x| ≤
      4608*M^3*eps*r := by
    have h := abs_physicalMixedDensityCorrection_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps r M 2 (by norm_num) heps hr.le hM0 hgeom.1 hH8 [i,j] (by simp) a
    norm_num [coordinateFieldWordPartial,mixedDensityCorrectionJetConstant] at h
    exact h
  have hc (i j a : Fin 3) :
      |r*Q i j*directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d a)) x| ≤ A := by
    rw [abs_mul,abs_mul,abs_of_pos hr]
    calc
      _ ≤ (r*(2*M))*(4608*M^3*eps*r) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hQ i j) hr.le) (hdd i j a) (abs_nonneg _) (by positivity)
      _ = A := by dsimp [A]; ring
  have hgraph0 : (U,U) ∈ spectralGraph hO hD (fun _ => (1 : ℝ)) := by
    intro k
    simp only [one_smul]
  have hU : ‖U‖ ≤ ‖U1‖ := by
    have h := norm_spectralGraph_output_le hO hD (fun _ => (1 : ℝ)) (besselWeight 1)
      1 (by norm_num) (fun k => by
        rw [abs_of_nonneg (show 0 ≤ (1 : ℝ) by norm_num),abs_of_pos (besselWeight_pos 1 k),one_mul]
        simpa only [besselWeight,Real.rpow_zero] using besselWeight_mono 0 1 (by norm_num) k)
      U U U1 hgraph0 (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
    simpa only [one_mul] using h
  have hNorm (a : Fin 3) : ‖ambientDerivativeField hF hO hD a G hG x‖ ≤ 2*‖U1‖ :=
    (normalizedDerivative hF hO hD a).le_of_opNorm_le (norm_normalizedDerivative_le hF hO hD a) U1
  have hMass : ‖U1‖^2 ≤ NN := by
    have hb0 : 0 ≤ beta x := le_trans zero_le_one hbeta
    have hbs : 1 ≤ (beta x)^2 := by nlinarith only [hbeta]
    have hs : ‖U1‖^2 ≤ (beta x)^2*‖U1‖^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hbs (sq_nonneg ‖U1‖)
    have h0 : 0 ≤ ∑ k : Fin 3, ‖v0 k‖^2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg (‖v0 k‖ : ℝ))
    have hhalf : 0 ≤ ∑ k : Fin 3, ‖vh k‖^2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg (‖vh k‖ : ℝ))
    have hh : 0 ≤ (beta x)⁻¹*(∑ k : Fin 3, ‖vh k‖^2) :=
      mul_nonneg (inv_nonneg.mpr hb0) hhalf
    have h3 : 0 ≤ beta x*‖U3‖^2 := mul_nonneg hb0 (sq_nonneg (‖U3‖ : ℝ))
    change ‖U1‖^2 ≤ (∑ k : Fin 3, ‖v0 k‖^2)+(beta x)^2*‖U1‖^2+
      (beta x)⁻¹*(∑ k : Fin 3, ‖vh k‖^2)+beta x*‖U3‖^2
    calc
      _ ≤ (beta x)^2*‖U1‖^2 := hs
      _ ≤ (∑ k : Fin 3, ‖v0 k‖^2)+(beta x)^2*‖U1‖^2 := le_add_of_nonneg_left h0
      _ ≤ (∑ k : Fin 3, ‖v0 k‖^2)+(beta x)^2*‖U1‖^2+
          (beta x)⁻¹*(∑ k : Fin 3, ‖vh k‖^2) := le_add_of_nonneg_right hh
      _ ≤ (∑ k : Fin 3, ‖v0 k‖^2)+(beta x)^2*‖U1‖^2+
          (beta x)⁻¹*(∑ k : Fin 3, ‖vh k‖^2)+beta x*‖U3‖^2 := le_add_of_nonneg_right h3
  have hField : |⟪mixedDensityScalarZeroField hF hO hD g1 g2 L lam δ R p G hG x,U⟫_ℝ| ≤
      54*A*NN :=
    OAI.AnisotropicCalderon.ScalarHilbertFormBounds.abs_real_inner_neg_triple_sum_smul_le
      (E := SphereL2)
      (fun i j a => r*Q i j*directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection j) (d a)) x)
      (fun a => ambientDerivativeField hF hO hD a G hG x) U U1 A NN hA hc hNorm hU hMass
  change |referenceDensityFamily g1 L (lam,x)*
      ⟪mixedDensityScalarZeroField hF hO hD g1 g2 L lam δ R p G hG x,U⟫_ℝ| ≤
    497664*M^4*eps*r^2*(referenceDensityFamily g1 L (lam,x)*NN)
  rw [abs_mul,abs_of_pos hMu]
  calc
    _ ≤ referenceDensityFamily g1 L (lam,x)*(54*A*NN) := mul_le_mul_of_nonneg_left hField hMu.le
    _ = _ := by dsimp only [A]; ring

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
