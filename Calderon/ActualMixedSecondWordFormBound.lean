import Calderon.ActualMixedDensityRemainderProfile

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedSecondWordFormBound
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator BaseDensityAdjoint SectionFiveErrorForms
  ActualSupportLocalSecondForm ActualReferenceDDNormalizedCoefficient
  ActualAngularDerivativeRaisingCommutator ActualNormalizedSecondMixedCommutatorForm
  ActualNormalizedSecondMixedWeakPairing ActualMixedDensityCoefficientJets
  ActualMixedDensityRemainderForm ActualMixedDensityRemainderProfile ReferenceWeightedApproximation ConformalDepth

/-- The negative c*C_ab ordinary second-base word retained in E2. This is one
actual coefficient word, not an equality with the unconstructed full commutator. -/
def mixedSecondRawDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
    referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x *
    ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
        (ambientBesselField hO hD 1 (by norm_num) G hG)) x),ambientSphereL2 G hG x⟫_ℝ)

def mixedSecondPrincipalDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  referenceDensityFamily g1 L (lam,x)*mixedSecondHalfForm hF hO hD g1 g2 L lam G hG x

lemma contDiff_mixedSecondPrincipalDensity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG) := by
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hhalf := contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG
  have he : mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG = fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        referenceDensityFamily g1 L (lam,x)*mixedSecondWordCoefficient g1 g2 L lam i j a b x *
        ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
          (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
          directionalFDeriv (coordinateDirection i) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x⟫_ℝ := by
    funext x
    simp only [mixedSecondPrincipalDensity,mixedSecondHalfForm,mixedSecondWordNormalizedCoefficient,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,sum_inner,real_inner_smul_left,
      Finset.mul_sum,mul_assoc]
  rw [he]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact (hmu.mul (contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b)).mul
    (((normalizedDerivativeRaisingCommutator hF hO hD a b).contDiff.comp
      (contDiff_directionalFDeriv (coordinateDirection j) _ hhalf)).inner ℝ
      (contDiff_directionalFDeriv (coordinateDirection i) _ hhalf))

lemma mixedSecondPrincipalDensity_eq_zero_outside
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG x = 0 := by
  have hgrad (k : Fin 3) : directionalFDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x = 0 :=
    ambientBesselField_directionalFDeriv_eq_zero_outside hO hD (1/2) (by norm_num) G hG K hK hz x hx (coordinateDirection k)
  unfold mixedSecondPrincipalDensity mixedSecondHalfForm
  simp only [hgrad,map_zero,inner_zero_right,Finset.sum_const_zero,mul_zero]

theorem abs_integral_mixedSecondPrincipalDensity_le_coordinate_norm
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (K : Set R3) (hK : IsCompact K) (eps eta M : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta) (hM : 1 ≤ M)
    (hgeom : ∀ x ∈ K, MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : ∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x))
    (hsmall : ∀ x ∈ K, eps*referenceRadius δ R p L x ≤ 1)
    (hrb : ∀ x ∈ K, referenceRadius δ R p L x*actualReferenceBeta g1 L lam δ R p x ≤ eta)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    |∫ x, mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG x| ≤
      24300*M^2*eps*eta * mixedCoordinateNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG := by
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let NN : R3 → ℝ := mixedCoordinateNormSquareIntegrand hO hD beta G hG
  let F : R3 → ℝ := mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG
  have hBeta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hCont := (contDiff_mixedSecondPrincipalDensity hF hO hD g1 g2 hg1 hg2 L lam G hG).continuous
  have hSupp : HasCompactSupport F := HasCompactSupport.intro hK (fun x hx =>
    mixedSecondPrincipalDensity_eq_zero_outside hF hO hD g1 g2 L lam G hG K hK hz x hx)
  have hi : Integrable F := hCont.integrable_of_hasCompactSupport hSupp
  have hN : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*NN x) :=
    integrable_ambient_source_norm_on_compact hO hD g1 hg1 L lam beta hBeta hPos G hG K hK hz
  have hPoint (x : R3) : |F x| ≤ (24300*M^2*eps*eta)*
      (referenceDensityFamily g1 L (lam,x)*NN x) := by
    have hMu := referenceDensityFamily_pos g1 hg1 L (lam,x)
    have hNN : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hPos x).le _ _ _ _
    by_cases hx : x ∈ K
    · have h := abs_mixedSecondHalfForm_le_coordinate_integrand hF hO hD g1 g2 L lam x eps
        (referenceRadius δ R p L x) M (beta x) eta heps (referenceRadius_pos δ R p L x hδ hR).le
        (le_trans zero_le_one hM) (hPos x) heta (hsmall x hx) (hrb x hx)
        (hh x hx).1 (hgeom x hx).2.2.1 (hgeom x hx).1 G hG
      dsimp only [F,mixedSecondPrincipalDensity]
      rw [abs_mul,abs_of_pos hMu]
      exact (mul_le_mul_of_nonneg_left h hMu.le).trans_eq (by dsimp [NN,mixedCoordinateNormSquareIntegrand]; ring)
    · dsimp only [F]
      rw [mixedSecondPrincipalDensity_eq_zero_outside hF hO hD g1 g2 L lam G hG K hK hz x hx]
      simp only [abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hMu.le hNN)
  have hNid : mixedCoordinateNormSquare hO hD g1 L lam beta G hG =
      ∫ x, referenceDensityFamily g1 L (lam,x)*NN x := by
    unfold mixedCoordinateNormSquare NN mixedCoordinateNormSquareIntegrand
    exact sourceNormSquare_eq_density_integral g1 hg1 L lam _ _ _ _ _
  change |∫ x, F x| ≤ 24300*M^2*eps*eta*mixedCoordinateNormSquare hO hD g1 L lam beta G hG
  rw [hNid]
  calc
    _ ≤ ∫ x, |F x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, (24300*M^2*eps*eta)*(referenceDensityFamily g1 L (lam,x)*NN x) :=
      integral_mono hi.abs (hN.const_mul _) hPoint
    _ = _ := integral_const_mul _ _

/-- Exact compact identity for the complete retained raw mixed-second word.
Both the principal half form and differentiated-density remainder are present. -/
theorem compact_mixedSecondRaw_word_identity
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x) =
      (∫ x, mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG x) +
      (∫ x, mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x) := by
  let phi := ambientSphereL2 G hG
  let half := ambientBesselField hO hD (1/2) (by norm_num) G hG
  let one := ambientBesselField hO hD 1 (by norm_num) G hG
  let mu : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)
  let c : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := mixedSecondWordCoefficient g1 g2 L lam
  let Rterm : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j a b x =>
    mu x*c i j a b x*⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) one) x),phi x⟫_ℝ
  let Pterm : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j a b x =>
    mu x*c i j a b x*⟪normalizedDerivativeRaisingCommutator hF hO hD a b
      (directionalFDeriv (coordinateDirection j) half x),directionalFDeriv (coordinateDirection i) half x⟫_ℝ
  let Dterm : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j a b x =>
    directionalFDeriv (coordinateDirection i) (fun y => mu y*c i j a b y) x *
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b
        (directionalFDeriv (coordinateDirection j) half x),half x⟫_ℝ
  have hphi := contDiff_ambientSphereL2 G hG
  have hhalf := contDiff_ambientBesselField hO hD (1/2) (by norm_num) G hG
  have hone := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hcphi := hasCompactSupport_ambientSphereL2 G hG K hK hz
  have hchalf := hasCompactSupport_ambientBesselField hO hD (1/2) (by norm_num) G hG K hK hz
  have hmu : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hc (i j a b : Fin 3) : ContDiff ℝ ∞ (c i j a b) :=
    contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b
  have hpair (w : R3 → ℝ) (u v : R3 → SphereL2) (hw : ContDiff ℝ ∞ w)
      (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvComp : HasCompactSupport v) :
      Integrable (fun x => w x*⟪u x,v x⟫_ℝ) := by
    have h := BaseDensityAdjoint.compact_inner_integrable (fun x => w x • u x) v
      (hw.smul hu).continuous hv.continuous hvComp
    simpa only [real_inner_smul_left] using h
  have hR (i j a b : Fin 3) : Integrable (Rterm i j a b) :=
    hpair (fun x => mu x*c i j a b x) _ phi (hmu.mul (hc i j a b))
      ((normalizedDerivativeRaisingCommutator hF hO hD a b).contDiff.comp
        (contDiff_directionalFDeriv (coordinateDirection i) _ (contDiff_directionalFDeriv (coordinateDirection j) _ hone)))
      hphi hcphi
  have hP (i j a b : Fin 3) : Integrable (Pterm i j a b) :=
    hpair (fun x => mu x*c i j a b x) _ _ (hmu.mul (hc i j a b))
      ((normalizedDerivativeRaisingCommutator hF hO hD a b).contDiff.comp
        (contDiff_directionalFDeriv (coordinateDirection j) _ hhalf))
      (contDiff_directionalFDeriv (coordinateDirection i) _ hhalf)
      (hchalf.fderiv_apply (𝕜 := ℝ) (coordinateDirection i))
  have hDterm (i j a b : Fin 3) : Integrable (Dterm i j a b) :=
    hpair (directionalFDeriv (coordinateDirection i) (fun x => mu x*c i j a b x)) _ half
      (contDiff_directionalFDeriv (coordinateDirection i) _ (hmu.mul (hc i j a b)))
      ((normalizedDerivativeRaisingCommutator hF hO hD a b).contDiff.comp
        (contDiff_directionalFDeriv (coordinateDirection j) _ hhalf)) hhalf hchalf
  have hsum (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
      (hF : ∀ i j a b, Integrable (F i j a b)) :
      (∫ x, ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, F i j a b x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∫ x, F i j a b x := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hF i j a b))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun a _ =>
      integrable_finset_sum _ (fun b _ => hF i j a b)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hF i j a b))]
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finset_sum _ (fun b _ => hF i j a b)
  have hslot (i j a b : Fin 3) : (∫ x, Rterm i j a b x) =
      -(∫ x, Pterm i j a b x)-(∫ x, Dterm i j a b x) :=
    compact_mixedSecondWord_raw_second_pairing hF hO hD g1 g2 hg1 hg2 L lam i j a b G hG K hK hz
  have hRaw : (∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∫ x, Rterm i j a b x) := by
    unfold mixedSecondRawDensity
    rw [integral_neg]
    exact congrArg Neg.neg (hsum Rterm hR)
  have hPrincipal : (∫ x, mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∫ x, Pterm i j a b x := by
    have he : mixedSecondPrincipalDensity hF hO hD g1 g2 L lam G hG =
        fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, Pterm i j a b x := by
      funext x
      simp only [mixedSecondPrincipalDensity,mixedSecondHalfForm,mixedSecondWordNormalizedCoefficient,
        ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,sum_inner,real_inner_smul_left,
        Finset.mul_sum,mul_assoc,Pterm,mu,c,half]
    rw [he]
    exact hsum Pterm hP
  have hRemainder : (∫ x, mixedDensityRemainderDensity hF hO hD g1 g2 L lam G hG x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∫ x, Dterm i j a b x :=
    hsum Dterm hDterm
  rw [hRaw,hPrincipal,hRemainder]
  simp_rw [hslot]
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  ring

theorem abs_integral_mixedSecondRawDensity_le_coordinate_norm
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (K : Set R3) (hK : IsCompact K) (eps eta M : ℝ) (heps : 0 ≤ eps) (heta : 0 ≤ eta) (hM : 1 ≤ M)
    (hgeom : ∀ x ∈ K, MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : ∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x))
    (hsmall : ∀ x ∈ K, eps*referenceRadius δ R p L x ≤ 1)
    (hr : ∀ x ∈ K, referenceRadius δ R p L x ≤ eta)
    (hrb : ∀ x ∈ K, referenceRadius δ R p L x*actualReferenceBeta g1 L lam δ R p x ≤ eta)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    |∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x| ≤
      359640*M^3*eps*eta * mixedCoordinateNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG := by
  have hP := abs_integral_mixedSecondPrincipalDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2
    L lam δ R p hL hδ hR hp K hK eps eta M heps heta hM hgeom hh hsmall hrb G hG hz
  have hRemainderBound := abs_integral_mixedDensityRemainderDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2
    L lam δ R p hL hδ hR hp K hK eps eta M heps heta hM hgeom hh hsmall hr G hG hz
  have hN : 0 ≤ mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG := by
    unfold mixedCoordinateNormSquare sourceNormSquare
    apply integral_nonneg
    intro x
    exact sourceNormSquareIntegrand_nonneg _
      (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x).le _ _ _ _
  have hpow : M^2 ≤ M^3 := by
    have h := mul_le_mul_of_nonneg_left hM (sq_nonneg M)
    nlinarith only [h]
  have hScale := mul_le_mul_of_nonneg_right hpow
    (by positivity : 0 ≤ 24300*eps*eta*mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG)
  rw [compact_mixedSecondRaw_word_identity hF hO hD g1 g2 hg1 hg2 L lam G hG K hK hz]
  exact (abs_add_le _ _).trans ((add_le_add hP hRemainderBound).trans (by nlinarith only [hScale]))

theorem exists_actual_mixedSecondRaw_word_profile
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x)) →
        ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        |∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x| ≤
          C*eps*eta * mixedCoordinateNormSquare hO hD g1 L lam
            (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_background_first_jet_bound g1 hg1 L K hK
  obtain ⟨p0,hp02,hprofile⟩ := exists_fixed_mixed_density_radius_profile g1 hg1 L hL K hK
  let C : ℝ := 359640*M^3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,p0,hp02,?_⟩
  intro p hp eta heta heta1
  obtain ⟨R,hR,hr⟩ := hprofile p hp eta heta heta1
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 g2 hg2 eps heps heps1 hh G hG hz
  have hp1 : 1 ≤ p := by omega
  have hsmall (x : R3) (hx : x ∈ K) : eps*referenceRadius δ R p L x ≤ 1 := by
    have hrad := (hr lam hlam δ hδ hδ1 x hx).2.2
    have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
    have hscale : eps*referenceRadius δ R p L x ≤ referenceRadius δ R p L x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heps1 hrpos
    exact hscale.trans (hrad.trans heta1)
  have hrb (x : R3) (hx : x ∈ K) : referenceRadius δ R p L x*actualReferenceBeta g1 L lam δ R p x ≤ eta := by
    have hbet := (hr lam hlam δ hδ hδ1 x hx).1
    have hsq : actualReferenceBeta g1 L lam δ R p x ≤ (actualReferenceBeta g1 L lam δ R p x)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsq (referenceRadius_pos δ R p L x hδ hR).le).trans
      (hr lam hlam δ hδ hδ1 x hx).2.1
  exact abs_integral_mixedSecondRawDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2 L lam δ R p
    hL hδ hR hp1 K hK eps eta M heps heta.le hM (fun x hx => hgeom lam hlam x hx)
    hh hsmall (fun x hx => (hr lam hlam δ hδ hδ1 x hx).2.2) hrb G hG hz

end OAI.AnisotropicCalderon.ActualMixedSecondWordFormBound
