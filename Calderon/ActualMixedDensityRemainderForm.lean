import Calderon.ActualMixedDensityCoefficientJets
import Calderon.ReferenceWeightedApproximation
import Calderon.SectionFiveErrorBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityRemainderForm
open SphereHarmonic SphereHilbertDecomposition SpectralWeightedGraph SpectralWeightComparison
  SmoothSphereFields SmoothAngularApplication SmoothMetricFrame ReferenceDensityBounds
  PrincipalCommutator BaseDensityAdjoint SectionFiveErrorForms ActualSupportLocalSecondForm
  ActualAngularDerivativeRaisingCommutator ActualMixedDensityCoefficientJets
  ActualNormalizedSecondMixedCommutatorForm ActualNormalizedSecondMixedWeakPairing
  ReferenceWeightedApproximation ConformalDepth

def mixedCoordinateNormSquareIntegrand
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (beta : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  sourceNormSquareIntegrand (beta x)
    (fun k : Fin 3 => directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (fun k : Fin 3 => directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG x)

def mixedCoordinateNormSquare
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (beta : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  sourceNormSquare g L lam beta
    (fun x k => directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun x k => directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG)

/-- The complete differentiated-density mixed remainder, in its literal weak form. -/
def mixedDensityRemainderDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
    directionalFDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g1 L (lam,y)*mixedSecondWordCoefficient g1 g2 L lam i j a b y) x *
    ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
      ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ

lemma norm_ambientBesselHalf_le_threeHalf
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖ambientBesselField hO hD (1/2) (by norm_num) G hG x‖ ≤
      ‖ambientBesselField hO hD (3/2) (by norm_num) G hG x‖ := by
  have h := norm_spectralGraph_output_le hO hD (besselWeight (1/2)) (besselWeight (3/2))
    1 (by norm_num) (fun k => by
      rw [abs_of_pos (besselWeight_pos (1/2) k),abs_of_pos (besselWeight_pos (3/2) k),one_mul]
      exact besselWeight_mono (1/2) (3/2) (by norm_num) k)
    (ambientSphereL2 G hG x) (ambientBesselField hO hD (1/2) (by norm_num) G hG x)
    (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)
    (ambientBesselField_graph hO hD (3/2) (by norm_num) G hG x)
  simpa only [one_mul] using h

lemma mixedDensityRemainderDensity_eq_normalized
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x =
      referenceDensityFamily g1 L (lam,x) *
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
        ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
          (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
          ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ) := by
  have hp := (referenceDensityFamily_pos g1 hg1 L (lam,x)).ne'
  unfold mixedDensityRemainderDensity mixedDensityDerivativeCoefficient
  simp only [Finset.mul_sum,← mul_assoc,mul_inv_cancel₀ hp,one_mul]

theorem abs_mixedDensityRemainderDensity_le_integrand
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (beta : R3 → ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 1 ≤ M) (hsmall : eps*radius ≤ 1)
    (hbeta : 0 < beta x) (hgeom : MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : MixedMetricFirstJetBound g1 g2 L lam x eps radius)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    |mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x| ≤
      335340*M^3*eps*radius *
        (referenceDensityFamily g1 L (lam,x)*mixedCoordinateNormSquareIntegrand hO hD beta G hG x) := by
  let v : Fin 3 → SphereL2 := fun j => directionalFDeriv (coordinateDirection j)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG) x
  let H : ℝ := ‖ambientBesselField hO hD (3/2) (by norm_num) G hG x‖
  let A : ℝ := 276*M^3*eps*radius
  let Y : Fin 3 → ℝ := fun j => (beta x)⁻¹*‖v j‖^2+(beta x)*H^2
  let NN : ℝ := mixedCoordinateNormSquareIntegrand hO hD beta G hG x
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMu := referenceDensityFamily_pos g1 hg1 L (lam,x)
  have ht (i j a b : Fin 3) :
      |mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
        ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
          ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| ≤ 15*A*Y j := by
    have hq := abs_mixedDensityDerivativeCoefficient_le g1 g2 hg1 hg2 L lam x eps radius M
      heps hradius hM hsmall hgeom hh i i j a b
    have hi : |⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
        ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| ≤ 15*Y j := by
      calc
        _ ≤ ‖normalizedDerivativeRaisingCommutator hF hO hD a b (v j)‖ *
            ‖ambientBesselField hO hD (1/2) (by norm_num) G hG x‖ := abs_real_inner_le_norm _ _
        _ ≤ (15*‖v j‖)*H := mul_le_mul
          ((normalizedDerivativeRaisingCommutator hF hO hD a b).le_of_opNorm_le
            (norm_normalizedDerivativeRaisingCommutator_le hF hO hD a b) _)
          (norm_ambientBesselHalf_le_threeHalf hO hD G hG x) (norm_nonneg _) (by positivity)
        _ = 15*(‖v j‖*H) := by ring
        _ ≤ 15*Y j := mul_le_mul_of_nonneg_left (mul_le_weighted_sq (beta x) ‖v j‖ H hbeta) (by norm_num)
    rw [abs_mul]
    calc
      _ ≤ A*(15*Y j) := mul_le_mul hq hi (abs_nonneg _) hA
      _ = _ := by ring
  have hcount : (∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, 15*A*Y j) =
      405*A*(∑ j : Fin 3, Y j) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin 3, 405*A*Y j := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hY : (∑ j : Fin 3, Y j) ≤ 3*NN := by
    have hAng := angular_error_terms_le_sourceNormSquareIntegrand (beta x)
      (fun k : Fin 3 => directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x) v
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
    have hGrad : 0 ≤ (beta x)⁻¹*(∑ j : Fin 3, ‖v j‖^2) := by positivity
    have he : (∑ j : Fin 3, Y j) = (beta x)⁻¹*(∑ j : Fin 3, ‖v j‖^2)+3*(beta x)*H^2 := by
      dsimp [Y]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
    change (beta x)⁻¹*(∑ j : Fin 3, ‖v j‖^2)+(beta x)*H^2 ≤ NN at hAng
    rw [he]
    nlinarith only [hAng,hGrad]
  rw [mixedDensityRemainderDensity_eq_normalized hF hO hD g1 g2 hg1 L lam G hG x,abs_mul,abs_of_pos hMu]
  change referenceDensityFamily g1 L (lam,x) * |∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
    mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
    ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
      ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| ≤ _
  have hSum : |∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
        ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| ≤ 405*A*(∑ j : Fin 3, Y j) := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
          mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
          ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
            ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |∑ a : Fin 3, ∑ b : Fin 3,
          mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
          ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
            ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, |∑ b : Fin 3,
          mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
          ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
            ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
          |mixedDensityDerivativeCoefficient g1 g2 L lam i i j a b x *
          ⟪normalizedDerivativeRaisingCommutator hF hO hD a b (v j),
            ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ| :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum
          (fun _ _ => Finset.abs_sum_le_sum_abs _ _)))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, 15*A*Y j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
          (fun a _ => Finset.sum_le_sum (fun b _ => ht i j a b))))
      _ = _ := hcount
  calc
    _ ≤ referenceDensityFamily g1 L (lam,x)*(405*A*(∑ j : Fin 3, Y j)) :=
      mul_le_mul_of_nonneg_left hSum hMu.le
    _ ≤ referenceDensityFamily g1 L (lam,x)*(405*A*(3*NN)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by positivity)) hMu.le
    _ = _ := by dsimp [A,NN]; ring

lemma contDiff_mixedDensityRemainderDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG) := by
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hhalf := contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG
  unfold mixedDensityRemainderDensity
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact (contDiff_directionalFDeriv (coordinateDirection i) _
    (hmu.mul (contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b))).mul
    (((normalizedDerivativeRaisingCommutator hF hO hD a b).contDiff.comp
      (contDiff_directionalFDeriv (coordinateDirection j) _ hhalf)).inner ℝ hhalf)

lemma mixedDensityRemainderDensity_eq_zero_outside
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x = 0 := by
  unfold mixedDensityRemainderDensity
  simp only [ambientBesselField_eq_zero hO hD (1/2) (by norm_num) G hG K hz x hx,
    inner_zero_right,mul_zero,Finset.sum_const_zero]

theorem abs_integral_mixedDensityRemainderDensity_le_coordinate_norm
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (K : Set R3) (hK : IsCompact K) (eps eta M : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta) (hM : 1 ≤ M)
    (hgeom : ∀ x ∈ K, MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : ∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x))
    (hsmall : ∀ x ∈ K, eps*referenceRadius δ R p L x ≤ 1)
    (hr : ∀ x ∈ K, referenceRadius δ R p L x ≤ eta)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    |∫ x, mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x| ≤
      335340*M^3*eps*eta * mixedCoordinateNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG := by
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let NN : R3 → ℝ := mixedCoordinateNormSquareIntegrand hO hD beta G hG
  let F : R3 → ℝ := mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG
  have hBeta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hCont := (contDiff_mixedDensityRemainderDensity hF hO hD g1 g2 hg1 hg2 L lam G hG).continuous
  have hSupp : HasCompactSupport F := HasCompactSupport.intro hK (fun x hx =>
    mixedDensityRemainderDensity_eq_zero_outside hF hO hD g1 g2 L lam G hG K hz x hx)
  have hi : Integrable F := hCont.integrable_of_hasCompactSupport hSupp
  have hN : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*NN x) :=
    integrable_ambient_source_norm_on_compact hO hD g1 hg1 L lam beta hBeta hPos G hG K hK hz
  have hPoint (x : R3) : |F x| ≤ (335340*M^3*eps*eta)*
      (referenceDensityFamily g1 L (lam,x)*NN x) := by
    have hMu := referenceDensityFamily_pos g1 hg1 L (lam,x)
    have hNN : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hPos x).le _ _ _ _
    by_cases hx : x ∈ K
    · have h := abs_mixedDensityRemainderDensity_le_integrand hF hO hD g1 g2 hg1 hg2 L lam x
        eps (referenceRadius δ R p L x) M beta heps (referenceRadius_pos δ R p L x hδ hR).le
        hM (hsmall x hx) (hPos x) (hgeom x hx) (hh x hx) G hG
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hr x hx) (by positivity)) (mul_nonneg hMu.le hNN))
    · dsimp only [F]
      rw [mixedDensityRemainderDensity_eq_zero_outside hF hO hD g1 g2 L lam G hG K hz x hx]
      simp only [abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hMu.le hNN)
  have hNid : mixedCoordinateNormSquare hO hD g1 L lam beta G hG =
      ∫ x, referenceDensityFamily g1 L (lam,x)*NN x := by
    unfold mixedCoordinateNormSquare NN mixedCoordinateNormSquareIntegrand
    exact sourceNormSquare_eq_density_integral g1 hg1 L lam _ _ _ _ _
  change |∫ x, F x| ≤ 335340*M^3*eps*eta*mixedCoordinateNormSquare hO hD g1 L lam beta G hG
  rw [hNid]
  calc
    _ ≤ ∫ x, |F x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, (335340*M^3*eps*eta)*(referenceDensityFamily g1 L (lam,x)*NN x) :=
      integral_mono hi.abs (hN.const_mul _) hPoint
    _ = _ := integral_const_mul _ _

end OAI.AnisotropicCalderon.ActualMixedDensityRemainderForm
