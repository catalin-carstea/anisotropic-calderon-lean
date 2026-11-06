import Calderon.ActualBalancedFirstPrincipalError
import Calderon.ReferenceWeightedApproximation

noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualSupportLocalSecondForm
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BalancedAngularShift BalancedFrameAngularShift SmoothMetricFrame
  ReferenceDensityBounds PrincipalCommutator ActualScalarPrincipalAdjoint
  ActualPerturbedDefect PerturbedDensityAdjoint ConformalDepth RadiusProfile
  AmbientAngularShift SmoothSphereFields SmoothAngularApplication SectionFiveErrorForms
  BaseDensityAdjoint WeightedBaseSpectral ActualBalancedFirstPrincipalError

def firstPrincipalContribution (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  ⟪directionalFDeriv (coordinateDirection k)
      (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x •
    (-(∑ b, frameEntry g L b k (lam,x) •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
        (ambientDerivativeField hF hO hD b G hG)) x)),ambientSphereL2 G hG x⟫_ℝ

lemma directionalDeriv_eq_zero_off_support
    (phi : R3 → SphereL2) (K : Set R3) (hsupp : tsupport phi ⊆ K)
    (v x : R3) (hx : x ∉ K) : directionalDeriv v phi x = 0 := by
  by_contra hn
  have hxderiv : x ∈ tsupport (directionalDeriv v phi) :=
    subset_closure (show x ∈ Function.support (directionalDeriv v phi) from hn)
  exact hx (hsupp ((tsupport_fderiv_apply_subset ℝ v) hxderiv))

lemma actualBeta_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hp : 1 ≤ p) (x : R3) : 0 < actualBeta g L lam δ R p x := by
  exact ReferenceWeightedApproximation.actualReferenceBeta_pos
    g hg L lam δ R p hL hδ hR hp x

theorem exists_density_directional_bound_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cmu : ℝ, 0 < Cmu ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i,
      |directionalDeriv (coordinateDirection i)
        (fun y => referenceDensityFamily g L (lam,y)) x| ≤
        Cmu * referenceDensityFamily g L (lam,x) := by
  obtain ⟨M,hM,hbounds⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨M^2, sq_pos_of_pos hMpos, ?_⟩
  intro lam hlam x hx i
  have hmu : 0 < referenceDensityFamily g L (lam,x) := referenceDensityFamily_pos g hg L (lam,x)
  have hd : |directionalDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g L (lam,y)) x| ≤ M := by
    simpa only [referenceBackgroundFamily,coordinateJetFamily,if_pos rfl,ite_true,
      familyDirectionalDeriv,directionalFDeriv,directionalDeriv] using
        hbounds lam hlam x hx (.inl 0) (.inr (.inl i))
  have hi : (referenceDensityFamily g L (lam,x))⁻¹ ≤ M := by
    have ht := hbounds lam hlam x hx (.inl 1) (.inl ())
    simpa [referenceBackgroundFamily,coordinateJetFamily,abs_of_pos (inv_pos.mpr hmu)] using ht
  have h1 : 1 ≤ M * referenceDensityFamily g L (lam,x) := (inv_le_iff_one_le_mul₀ hmu).mp hi
  have hrel : M ≤ M^2 * referenceDensityFamily g L (lam,x) := by
    have hm := mul_le_mul_of_nonneg_left h1 hMpos.le
    nlinarith
  exact hd.trans hrel

theorem compact_normalized_half_second_form_bound_on_support
    {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (directions : ι → R3) (i j : ι) (beta : R3 → ℝ)
    (hbeta : ContDiff ℝ ∞ beta) (hpos : ∀ x, 0 < beta x)
    (room : Set R3) (hbeta1 : ∀ x ∈ room, 1 ≤ beta x)
    (phi phiHalf phiOne phiThree : R3 → SphereL2)
    (hphiHalf : ContDiff ℝ ∞ phiHalf) (hcompact : HasCompactSupport phiHalf)
    (hsupport : tsupport phiHalf ⊆ room)
    (hhalf : ∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2))
    (hthree : ∀ x, (phi x,phiThree x) ∈ sphereBesselGraph hO hD (3/2))
    (K : R3 → SphereL2 →L[ℝ] SphereL2) (hK : ContDiff ℝ ∞ K)
    (Cmu Cbeta Cw Cdw : ℝ)
    (hCmu : 0 ≤ Cmu) (hCbeta : 0 ≤ Cbeta) (hCw : 0 ≤ Cw) (hCdw : 0 ≤ Cdw)
    (hKbound : ∀ x ∈ room, ‖K x‖ ≤ Cw * epsilon)
    (hDKbound : ∀ x ∈ room,
      ‖fderiv ℝ K x (directions i)‖ ≤ Cdw * epsilon * beta x)
    (hdmu : ∀ x ∈ room,
      |directionalDeriv (directions i) (fun y => referenceDensityFamily g L (lam,y)) x|
        ≤ Cmu * referenceDensityFamily g L (lam,x))
    (hdbeta : ∀ x ∈ room, |directionalDeriv (directions i) beta x| ≤ Cbeta * beta x^2)
    (hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (directions k) phi x)
        (phiOne x) (fun k => directionalDeriv (directions k) phiHalf x) (phiThree x))) :
    |∫ x, referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
      ⟪directionalDeriv (directions i) (directionalDeriv (directions j) phiHalf) x,
        K x (phiHalf x)⟫_ℝ| ≤
      epsilon * (Cw+(Cmu+Cbeta)*Cw+Cdw) *
        sourceNormSquare g L lam beta (fun x k => directionalDeriv (directions k) phi x)
          phiOne (fun x k => directionalDeriv (directions k) phiHalf x) phiThree := by
  classical
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let h : R3 → ℝ := fun x => mu x * (beta x)⁻¹
  let W : R3 → SphereL2 := fun x => K x (phiHalf x)
  let G : R3 → ι → SphereL2 := fun x k => directionalDeriv (directions k) phiHalf x
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (directions k) phi x) (phiOne x) (G x) (phiThree x)
  let Bw : ℝ := Cw * epsilon
  let Bdw : ℝ := Cdw * epsilon
  have hBw : 0 ≤ Bw := mul_nonneg hCw hepsilon
  have hBdw : 0 ≤ Bdw := mul_nonneg hCdw hepsilon
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hinv : ContDiff ℝ ∞ (fun x => (beta x)⁻¹) := hbeta.inv (fun x => (hpos x).ne')
  have hh : ContDiff ℝ ∞ h := hmu.mul hinv
  have hW : ContDiff ℝ ∞ W := hK.clm_apply hphiHalf
  have hparts := compact_second_form_one_parts (directions i) (directions j) mu
    (fun x => (beta x)⁻¹) phiHalf W hmu hinv hphiHalf hW hcompact
  have hbound (x : R3) :
      |⟪directionalDeriv (directions i) (fun y => h y • W y) x,G x j⟫_ℝ| ≤
        (Bw+(Cmu+Cbeta)*Bw+Bdw) * (mu x*NN x) := by
    by_cases hx : x ∈ room
    ·
      have hmu0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
      have hh0 : 0 ≤ h x := mul_nonneg hmu0 (inv_nonneg.mpr (hpos x).le)
      have hN0 : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      have hhalfthree := norm_bessel_half_le_threehalf hO hD _ _ _ (hhalf x) (hthree x)
      have hproduct : ‖phiHalf x‖ * ‖G x j‖ ≤ NN x := by
        calc
          _ ≤ ‖phiThree x‖ * ‖G x j‖ := mul_le_mul_of_nonneg_right hhalfthree (norm_nonneg _)
          _ ≤ (beta x)⁻¹ * ‖G x j‖^2 + beta x * ‖phiThree x‖^2 := by
            simpa only [mul_comm] using mul_le_weighted_sq (beta x) ‖G x j‖ ‖phiThree x‖ (hpos x)
          _ ≤ (beta x)⁻¹ * (∑ k, ‖G x k‖^2) + beta x * ‖phiThree x‖^2 :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_sq_le_sum (G x) j)
              (inv_nonneg.mpr (hpos x).le)) le_rfl
          _ ≤ _ := angular_error_terms_le_sourceNormSquareIntegrand (beta x) _ _ _ _
      have hdhinv : |directionalDeriv (directions i) h x| ≤ mu x*(Cmu+Cbeta) := by
        dsimp [h]
        rw [directionalDeriv_mul (directions i) mu (fun y => (beta y)⁻¹) hmu hinv x]
        simpa only [mul_one,mul_zero,add_zero] using abs_density_weight_derivative_coefficient_le
          (beta x) (mu x) (directionalDeriv (directions i) mu x)
          (directionalDeriv (directions i) (fun y => (beta y)⁻¹) x) 1 0 Cmu Cbeta 1 0 1 1
          (hbeta1 x hx) hmu0 hCmu hCbeta (by norm_num) (by norm_num) (by norm_num) le_rfl
          (hdmu x hx) (abs_directionalDeriv_inv_le (directions i) beta hbeta x (hpos x) Cbeta (hdbeta x hx))
          (by norm_num) (by simp)
      have hp : |⟪h x • K x (G x i),G x j⟫_ℝ| ≤ mu x*Bw*NN x := by
        calc
          _ ≤ (|h x| * Bw) * (‖G x i‖*‖G x j‖) := abs_scaled_clm_inner_le (K x) (h x) Bw (hKbound x hx) _ _
          _ ≤ (|h x| * Bw) * (∑ k, ‖G x k‖^2) := mul_le_mul_of_nonneg_left
            (norm_mul_norm_le_sum (G x) i j) (mul_nonneg (abs_nonneg _) hBw)
          _ = (mu x*Bw) * ((beta x)⁻¹ * (∑ k, ‖G x k‖^2)) := by rw [abs_of_nonneg hh0]; dsimp [h]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (weighted_gradient_square_le_sourceNormSquareIntegrand (beta x) (hpos x).le _ _ _ _)
            (mul_nonneg hmu0 hBw)
      have hm : |⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ| ≤
          (mu x*(Cmu+Cbeta)*Bw)*NN x := by
        calc
          _ ≤ (|directionalDeriv (directions i) h x| * Bw) * (‖phiHalf x‖*‖G x j‖) :=
            abs_scaled_clm_inner_le (K x) _ Bw (hKbound x hx) _ _
          _ ≤ (mu x*(Cmu+Cbeta)*Bw) * NN x := mul_le_mul
            (mul_le_mul_of_nonneg_right hdhinv hBw) hproduct (by positivity) (by positivity)
      have hd : |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| ≤
          (mu x*Bdw)*NN x := by
        calc
          _ ≤ (|h x| * (Bdw*beta x)) * (‖phiHalf x‖*‖G x j‖) :=
            abs_scaled_clm_inner_le ((fderiv ℝ K x (directions i))) (h x) _ (hDKbound x hx) _ _
          _ = (mu x*Bdw) * (‖phiHalf x‖*‖G x j‖) := by
            rw [abs_of_nonneg hh0]
            dsimp [h]
            field_simp [(hpos x).ne'] <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hproduct (mul_nonneg hmu0 hBdw)
      have hF : directionalDeriv (directions i) (fun y => h y • W y) x =
          h x • K x (G x i) + directionalDeriv (directions i) h x • K x (phiHalf x) +
            h x • (fderiv ℝ K x (directions i)) (phiHalf x) := by
        rw [directionalDeriv_smul (directions i) h W hh hW x]
        change directionalDeriv (directions i) h x • K x (phiHalf x) +
          h x • directionalDeriv (directions i) (fun y => K y (phiHalf y)) x = _
        rw [directionalDeriv_clm_apply (directions i) K phiHalf hK hphiHalf x,smul_add]
        dsimp [G]
        abel
      rw [hF,inner_add_left,inner_add_left]
      calc
        _ ≤ |⟪h x • K x (G x i),G x j⟫_ℝ +
            ⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ| +
            |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| := abs_add_le _ _
        _ ≤ (|⟪h x • K x (G x i),G x j⟫_ℝ| +
            |⟪directionalDeriv (directions i) h x • K x (phiHalf x),G x j⟫_ℝ|) +
            |⟪h x • (fderiv ℝ K x (directions i)) (phiHalf x),G x j⟫_ℝ| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ ≤ (mu x*Bw*NN x+(mu x*(Cmu+Cbeta)*Bw)*NN x)+(mu x*Bdw)*NN x :=
          add_le_add (add_le_add hp hm) hd
        _ = _ := by ring
    · have hz : G x j = 0 := directionalDeriv_eq_zero_off_support
        phiHalf room hsupport (directions j) x hx
      have hmu0 : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (lam,x)).le
      have hN0 : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      simp only [hz,inner_zero_right,abs_zero]
      positivity
  have hint := norm_integral_le_of_norm_le
    (f := fun x => ⟪directionalDeriv (directions i) (fun y => h y • W y) x,G x j⟫_ℝ)
    (hN.const_mul (Bw+(Cmu+Cbeta)*Bw+Bdw))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,mu,NN,G] using hbound x))
  rw [integral_const_mul] at hint
  have hresult : |∫ x, mu x * (beta x)⁻¹ *
      ⟪directionalDeriv (directions i) (directionalDeriv (directions j) phiHalf) x,W x⟫_ℝ| ≤
      (Bw+(Cmu+Cbeta)*Bw+Bdw) * sourceNormSquare g L lam beta
        (fun x k => directionalDeriv (directions k) phi x) phiOne G phiThree := by
    rw [hparts,abs_neg,sourceNormSquare_eq_density_integral g hg L lam]
    simpa only [Real.norm_eq_abs,mu,h,NN,G] using hint
  calc
    _ ≤ (Bw+(Cmu+Cbeta)*Bw+Bdw) * sourceNormSquare g L lam beta
        (fun x k => directionalDeriv (directions k) phi x) phiOne G phiThree := hresult
    _ = _ := by dsimp only [Bw,Bdw]; ring

lemma integrable_ambient_source_norm_on_compact
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    let phi := ambientSphereL2 G hG
    let phiHalf := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
    let phiOne := ambientBesselField hO hD 1 (by norm_num) G hG
    let phiThree := ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun k => directionalDeriv (coordinateDirection k) phi x)
        (phiOne x) (fun k => directionalDeriv (coordinateDirection k) phiHalf x) (phiThree x)) := by
  dsimp only
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let phiOne : R3 → SphereL2 := ambientBesselField hO hD 1 (by norm_num) G hG
  let phiThree : R3 → SphereL2 := ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
  let NN : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (coordinateDirection k) phi x) (phiOne x)
    (fun k => directionalDeriv (coordinateDirection k) phiHalf x) (phiThree x)
  have hphi : ContDiff ℝ ∞ phi := contDiff_ambientSphereL2 G hG
  have hhalf : ContDiff ℝ ∞ phiHalf := contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hone : ContDiff ℝ ∞ phiOne := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hthree : ContDiff ℝ ∞ phiThree := contDiff_ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
  have hdphi (k : Fin 3) : Continuous (directionalDeriv (coordinateDirection k) phi) :=
    (contDiff_directionalDeriv _ _ hphi).continuous
  have hdhalf (k : Fin 3) : Continuous (directionalDeriv (coordinateDirection k) phiHalf) :=
    (contDiff_directionalDeriv _ _ hhalf).continuous
  have hinv : Continuous (fun x => (beta x)⁻¹) := hbeta.inv₀ (fun x => (hpos x).ne')
  have honeContinuous : Continuous phiOne := hone.continuous
  have hthreeContinuous : Continuous phiThree := hthree.continuous
  have hNN : Continuous NN := by
    dsimp only [NN,sourceNormSquareIntegrand]
    fun_prop
  have hsupp : tsupport phi ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    change phi x ≠ 0 at hx
    exact hx (ambientSphereL2_eq_zero G hG x (hz x hxK))
  have hsuppHalf : tsupport phiHalf ⊆ K :=
    tsupport_ambientBesselField_subset hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
  have hcNN : HasCompactSupport NN := HasCompactSupport.intro hK (fun x hx => by
    have hzero (k : Fin 3) : directionalDeriv (coordinateDirection k) phi x = 0 :=
      directionalDeriv_eq_zero_off_support phi K hsupp _ x hx
    have hhalfzero (k : Fin 3) : directionalDeriv (coordinateDirection k) phiHalf x = 0 :=
      directionalDeriv_eq_zero_off_support phiHalf K hsuppHalf _ x hx
    have honezero : phiOne x = 0 := ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx
    have hthreezero : phiThree x = 0 := ambientBesselField_eq_zero hO hD (3/2 : ℝ) (by norm_num) G hG K hz x hx
    simp [NN,sourceNormSquareIntegrand,hzero,hhalfzero,honezero,hthreezero])
  exact ((continuous_referenceBaseDensity g hg L lam).mul hNN).integrable_of_hasCompactSupport hcNN.mul_left

lemma firstPrincipalContribution_eq_normalized
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (k i j : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (hb : 0 < actualBeta g L lam δ R p x) :
    firstPrincipalContribution hF hO hD g L lam δ R p h k i j G hG x =
      (actualBeta g L lam δ R p x)⁻¹ *
        ⟪directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)) x,
          normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j x
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG x)⟫_ℝ := by
  exact actual_first_principal_ambient_pair hF hO hD g L lam δ R p h k i j G hG x hb

theorem exists_actual_first_principal_support_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ actualBeta g L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualBeta g L lam δ R p x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      ∀ k i j,
      |∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h k i j G hG x| ≤ eps * C *
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := by
  obtain ⟨Cw,Cdw,hCw,hCdw,hbounds⟩ :=
    exists_normalizedFirstPrincipal_uniform_bounds hF hO hD g hg L hL K hK
  obtain ⟨Cmu,hCmu,hdensity⟩ := exists_density_directional_bound_on_compact g hg L K hK
  obtain ⟨D,hDpos,hbetaDer⟩ := exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨Cw+(Cmu+D)*Cw+Cdw, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz k i j
  let beta : R3 → ℝ := actualBeta g L lam δ R p
  let phi : R3 → SphereL2 := ambientSphereL2 G hG
  let phiHalf : R3 → SphereL2 := ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  let phiOne : R3 → SphereL2 := ambientBesselField hO hD 1 (by norm_num) G hG
  let phiThree : R3 → SphereL2 := ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG
  let KK : R3 → SphereL2 →L[ℝ] SphereL2 :=
    normalizedFirstPrincipalRaising hF hO hD g L lam δ R p h k i j
  have hbeta : ContDiff ℝ ∞ beta := contDiff_actualBeta g hg L lam δ R p hL hδ hR
  have hpos (x : R3) : 0 < beta x := actualBeta_pos g hg L lam δ R p hL hδ hR hp x
  have hKK : ContDiff ℝ ∞ KK :=
    contDiff_normalizedFirstPrincipalRaising hF hO hD g hg L lam δ R p h k i j hL hδ hR hh
  have hKb (x : R3) (hx : x ∈ K) : ‖KK x‖ ≤ Cw * eps :=
    (hbounds lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
      (hb x hx) (hsmall x hx) k i j i).2.1
  have hDKb (x : R3) (hx : x ∈ K) :
      ‖fderiv ℝ KK x (coordinateDirection i)‖ ≤ Cdw * eps * beta x :=
    (hbounds lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
      (hb x hx) (hsmall x hx) k i j i).2.2.2
  have hdbeta (x : R3) (hx : x ∈ K) :
      |directionalDeriv (coordinateDirection i) beta x| ≤ D * beta x^2 := by
    have hn : ‖fderiv ℝ beta x‖ ≤ D * beta x^2 := (hbetaDer lam hlam δ hδ hδ1 R hR p hp x hx).1
    have ht := (fderiv ℝ beta x).le_opNorm (coordinateDirection i)
    simpa only [directionalDeriv,Real.norm_eq_abs,norm_coordinateDirection,mul_one] using
      ht.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hhalfSmooth : ContDiff ℝ ∞ phiHalf :=
    contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
  have hhalfCompact : HasCompactSupport phiHalf :=
    hasCompactSupport_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
  have hhalfSupport : tsupport phiHalf ⊆ K :=
    tsupport_ambientBesselField_subset hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
  have hN : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      sourceNormSquareIntegrand (beta x) (fun l => directionalDeriv (coordinateDirection l) phi x)
        (phiOne x) (fun l => directionalDeriv (coordinateDirection l) phiHalf x) (phiThree x)) :=
    integrable_ambient_source_norm_on_compact hO hD g hg L lam beta hbeta.continuous hpos G hG K hK hz
  have hestimate := compact_normalized_half_second_form_bound_on_support hO hD g hg L lam eps heps
    coordinateDirection i j beta hbeta hpos K hb phi phiHalf phiOne phiThree hhalfSmooth
    hhalfCompact hhalfSupport
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG)
    (ambientBesselField_graph hO hD (3/2 : ℝ) (by norm_num) G hG)
    KK hKK Cmu D Cw Cdw hCmu.le hDpos.le hCw.le hCdw.le hKb hDKb
    (fun x hx => hdensity lam hlam x hx i) hdbeta hN
  calc
    _ = |∫ x, referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
        ⟪directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j) phiHalf) x,
          KK x (phiHalf x)⟫_ℝ| := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change referenceDensityFamily g L (lam,x) *
            firstPrincipalContribution hF hO hD g L lam δ R p h k i j G hG x =
          referenceDensityFamily g L (lam,x) * (beta x)⁻¹ *
            ⟪directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j) phiHalf) x,
              KK x (phiHalf x)⟫_ℝ
        rw [firstPrincipalContribution_eq_normalized hF hO hD g L lam δ R p h k i j G hG x (hpos x)]
        dsimp only [beta,KK,phiHalf]
        ring)
    _ ≤ _ := hestimate

theorem exists_actual_first_principal_sum_support_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ actualBeta g L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualBeta g L lam δ R p x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      |∑ t : Fin 3 × Fin 3 × Fin 3, ∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x| ≤ eps * C *
        sourceNormSquare g L lam (actualBeta g L lam δ R p)
          (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
          (ambientBesselField hO hD 1 (by norm_num) G hG)
          (fun x k => directionalDeriv (coordinateDirection k)
            (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
          (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) := by
  classical
  obtain ⟨C,hC,hbounds⟩ := exists_actual_first_principal_support_bound hF hO hD g hg L hL K hK
  refine ⟨27*C, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  let NN : ℝ := sourceNormSquare g L lam (actualBeta g L lam δ R p)
    (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun x k => directionalDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG)
  have hcomponent (t : Fin 3 × Fin 3 × Fin 3) :
      |∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x| ≤ eps*C*NN :=
    hbounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz t.1 t.2.1 t.2.2
  calc
    _ ≤ ∑ t : Fin 3 × Fin 3 × Fin 3, |∫ x, referenceDensityFamily g L (lam,x) *
        firstPrincipalContribution hF hO hD g L lam δ R p h t.1 t.2.1 t.2.2 G hG x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin 3 × Fin 3 × Fin 3, eps*C*NN :=
      Finset.sum_le_sum (fun t _ => hcomponent t)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
      norm_num <;> ring

end OAI.AnisotropicCalderon.ActualSupportLocalSecondForm
