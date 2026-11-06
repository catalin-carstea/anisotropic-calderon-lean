import Calderon.ActualFiniteHarmonicModelSecondAngularSymmetric
import Calderon.ActualFiniteHarmonicModelSecondAngularBounds
import Calderon.ActualFiniteHarmonicModelSecondBalancedAngularJets
import Calderon.ActualFiniteHarmonicModelMixedZeroScalarJets
import Calderon.ActualFiniteHarmonicModelFirstAngularBounds
import Calderon.ActualNormalizedSecondDriftDefectCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SpectralWeightedGraph ActualReferenceDDHigherSpectralGraphs SphereHarmonic ActualFiniteHarmonicCore BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherActualCoefficients ActualReferenceDDNormalizedCoefficient ActualReferenceParallelRaising
  ActualMixedDensityHigherCoefficientJets ActualMixedDensityScalarZeroForm ActualNormalizedPrincipalDensityCoefficientJets
  ActualNormalizedSecondDriftDefectCoefficients ActualNormalizedSecondDriftDefectWeightedJets
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelDefectCoefficients
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth
  CoordinateBootstrapJets MetricOperator ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWReversedBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWReversedBoundsFunction
theorem exists_nativeWSymmetricHalfAngularCoefficient_uniform_coordinate_word_smallness
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x‖ ≤
          (C * eps) * beta^w.length := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 4
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 4
  obtain ⟨CK,hCK,hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 3 (by norm_num)
  obtain ⟨Cm,hCm,hMixed⟩ := exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness
    g1 g2 hg1 hg2 L hL K hK
  obtain ⟨Cd,hCd,hDiv⟩ := exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_smallness
    g1 g2 hg1 hg2 L hL K hK 2
  let I : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  let T (a : Fin 3) := balancedDerivative hF hO hD a+balancedRaising hF hO hD a
  let MT : ℝ := 1+∑ a : Fin 3, ‖T a‖
  let Ca : ℝ := scalarAdjointZeroCoordinateJetConstant 2*Cr*M^3
  let C : ℝ := 1+8*Ca+8*Cd+192*M^2*CK+12*Cm*MT
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMT : 0 ≤ MT := by dsimp only [MT]; positivity
  have hCa : 0 ≤ Ca := by
    dsimp only [Ca,scalarAdjointZeroCoordinateJetConstant,
      weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]
    positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hT (a : Fin 3) : ‖T a‖ ≤ MT := by
    have ht := Finset.single_le_sum (fun b _ => norm_nonneg (T b)) (Finset.mem_univ a)
    dsimp only [MT]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw
  let r : ℝ := referenceRadius δ R p L x
  let Rate : ℝ := eps/beta
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have hRate : 0 ≤ Rate := div_nonneg heps hb0
  have hRateeps : Rate ≤ eps := (div_le_iff₀ hbpos).2 (by nlinarith)
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := by nlinarith [one_le_pow₀ hb (n := 2)]
  have hepsr1 : eps*r ≤ 1 := by nlinarith
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhe (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let mui : R3 → ℝ := fun y => (mu y)⁻¹
  let A : R3 → ℝ := fun y => adjointZeroCoefficient coordinateDirection mu
    (actualPrincipalMatrix g1 L lam δ R p h) y
  let B (j : Fin 3) := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  let BA (j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ContinuousLinearMap.adjoint (B j y)
  let Y (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (B j)
  let Div := ActualNormalizedSecondDriftNativeAdjunction.normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p
  have hmuS : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmuiS : ContDiff ℝ ∞ mui :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hAS : ContDiff ℝ ∞ A := contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hBS (j : Fin 3) : ContDiff ℝ ∞ (B j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hBAS (j : Fin 3) : ContDiff ℝ ∞ (BA j) := contDiff_angularAdjoint (B j) (hBS j)
  have hYS (j : Fin 3) : ContDiff ℝ ∞ (Y j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hmuS.smul (hBAS j))
  have hDivS : ContDiff ℝ ∞ Div :=
    ActualNormalizedSecondDriftNativeAdjunction.contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hAj : HasCoordinateWordJetBound 2 A x (Ca*eps) beta 0 := by
    intro v hv
    have ht := abs_actualScalarAdjointZero_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr 2 (by norm_num) hδ hR heps hM hCr.le hepsr1 hb
      (hgeom lam hlam x hx) (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8 v hv
    calc
      ‖coordinateFieldWordPartial v A x‖ = |coordinateFieldWordPartial v A x| := Real.norm_eq_abs _
      _ ≤ Ca*r*beta^(v.length+2) := by simpa only [A,Ca,mu,r,h] using ht
      _ = (Ca*(r*beta^2))*beta^v.length := by rw [pow_add]; ring
      _ ≤ (Ca*eps)*beta^(0+v.length) := by
        simpa only [Nat.zero_add] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hCa) (pow_nonneg hb0 _)
  have hBj (j : Fin 3) : HasCoordinateWordJetBound 3 (B j) x (CK*Rate) beta 0 := by
    intro v hv
    have ht := (hDD lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx
      hb hH8 hsmall v hv).1 j
    simpa only [B,Rate,beta,actualReferenceBeta,Nat.zero_add,mul_div_assoc] using ht
  have hBAj (j : Fin 3) : HasCoordinateWordJetBound 3 (BA j) x (CK*Rate) beta 0 := by
    intro v hv
    dsimp only [BA]
    rw [coordinateFieldWordPartial_adjoint (B j) (hBS j) v]
    exact ((ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
      (SphereL2 →L[ℝ] SphereL2)).norm_map (coordinateFieldWordPartial v (B j) x)).le.trans (hBj j v hv)
  have hmuj : HasCoordinateWordJetBound 3 mu x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx).1.2.2.1 v (by omega)
    have hnorm : ‖coordinateFieldWordPartial v mu x‖ ≤ M := by
      simpa only [Real.norm_eq_abs,mu] using ht
    exact hnorm.trans
      (by simpa only [Nat.zero_add,mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0)
  have hmuij : HasCoordinateWordJetBound 2 mui x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx).1.2.2.2 v (by omega)
    have hnorm : ‖coordinateFieldWordPartial v mui x‖ ≤ M := by
      simpa only [Real.norm_eq_abs,mui,mu] using ht
    exact hnorm.trans
      (by simpa only [Nat.zero_add,mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0)
  have hYj (j : Fin 3) : HasCoordinateWordJetBound 2 (Y j) x (8*M*CK*eps) beta 0 := by
    have hprod := hasCoordinateWordJetBound_smul 3 mu (BA j) hmuS (hBAS j)
      x M (CK*Rate) beta 0 0 hM0 (mul_nonneg hCK.le hRate) hb0 hmuj (hBAj j)
    have hprod' : HasCoordinateWordJetBound 3 (fun y => mu y • BA j y) x (8*M*CK*Rate) beta 0 := by
      convert hprod using 1 <;> simp only [show (2 : ℝ)^3=8 by norm_num,Nat.add_zero] <;> ring
    have hd := hasCoordinateWordJetBound_coordinate_derivative 2 (fun y => mu y • BA j y)
      x (8*M*CK*Rate) beta 0 j hprod'
    intro v hv
    have ht := hd v hv
    have he : (8*M*CK*Rate)*beta^(0+1+v.length) = (8*M*CK*eps)*beta^(0+v.length) := by
      simp only [Nat.zero_add,pow_add,pow_one,Rate]
      field_simp [hbpos.ne']
      <;> ring
    rw [he] at ht
    exact ht
  have hDivj : HasCoordinateWordJetBound 2 Div x (Cd*eps) beta 0 := by
    intro v hv
    have ht := hDiv lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall v hv
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRateeps hCd.le) (pow_nonneg hb0 v.length)
    have hnorm : ‖coordinateFieldWordPartial v Div x‖ ≤ (Cd*eps/beta)*beta^v.length := by
      simpa only [Real.norm_eq_abs,Div,beta,actualReferenceBeta] using ht
    exact hnorm.trans (by simpa only [Rate,Nat.zero_add,mul_div_assoc] using hscale)
  have hYAj (j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ContinuousLinearMap.adjoint (Y j y)) x (8*M*CK*eps) beta 0 := by
    intro v hv
    rw [coordinateFieldWordPartial_adjoint (Y j) (hYS j) v]
    exact ((ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
      (SphereL2 →L[ℝ] SphereL2)).norm_map (coordinateFieldWordPartial v (Y j) x)).le.trans (hYj j v hv)
  have hYPair (j : Fin 3) := hasCoordinateWordJetBound_add 2 (Y j)
    (fun y => ContinuousLinearMap.adjoint (Y j y)) (hYS j) (contDiff_angularAdjoint (Y j) (hYS j))
    x (8*M*CK*eps) (8*M*CK*eps) beta 0 (hYj j) (hYAj j)
  have hYPair' (j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => Y j y+ContinuousLinearMap.adjoint (Y j y)) x (16*M*CK*eps) beta 0 := by
    convert hYPair j using 1 <;> ring
  have hYSumS : ContDiff ℝ ∞ (fun y => ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y))) :=
    ContDiff.sum (fun j _ => (hYS j).add (contDiff_angularAdjoint (Y j) (hYS j)))
  have hYSum := hasCoordinateWordJetBound_sum 2 (fun j y => Y j y+ContinuousLinearMap.adjoint (Y j y))
    (fun j => (hYS j).add (contDiff_angularAdjoint (Y j) (hYS j))) x (16*M*CK*eps) beta 0 hYPair'
  have hYSum' : HasCoordinateWordJetBound 2
      (fun y => ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y))) x (48*M*CK*eps) beta 0 := by
    convert hYSum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hAdj := hasCoordinateWordJetBound_smul 2 mui
    (fun y => ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y))) hmuiS hYSumS x M
    (48*M*CK*eps) beta 0 0 hM0 (by positivity) hb0 hmuij hYSum'
  have hAdjj : HasCoordinateWordJetBound 2
      (fun y => mui y • ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y)))
      x (192*M^2*CK*eps) beta 0 := by
    convert hAdj using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hTwoI : ‖(2 : ℝ) • I‖ ≤ 2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show (0 : ℝ)<2 by norm_num)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_inverseDegreeMultiplier_le_one hO hD) (show (0 : ℝ)≤2 by norm_num)
  have hTwoIj : HasCoordinateWordJetBound 2 (fun _ : R3 => (2 : ℝ) • I) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 _ x 2 beta hTwoI hb0
  have hAD := hasCoordinateWordJetBound_sub 2 A Div hAS hDivS x (Ca*eps) (Cd*eps) beta 0 hAj hDivj
  have hAD' : HasCoordinateWordJetBound 2 (fun y => A y-Div y) x ((Ca+Cd)*eps) beta 0 := by
    convert hAD using 1 <;> ring
  have hADI := hasCoordinateWordJetBound_smul 2 (fun y => A y-Div y) (fun _ : R3 => (2 : ℝ) • I)
    (hAS.sub hDivS) contDiff_const x ((Ca+Cd)*eps) 2 beta 0 0 (by positivity) (by norm_num) hb0 hAD' hTwoIj
  have hADIj : HasCoordinateWordJetBound 2 (fun y => (A y-Div y) • ((2 : ℝ) • I))
      x (8*(Ca+Cd)*eps) beta 0 := by
    convert hADI using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  let dens (a : Fin 3) := physicalMixedDensityCorrection g1 L lam h a
  have hdensS (a : Fin 3) : ContDiff ℝ ∞ (dens a) := contDiff_physicalMixedDensityCorrection g1 hg1 L lam h hhe a
  have hdensj (a : Fin 3) : HasCoordinateWordJetBound 2 (dens a) x (Cm*eps) beta 0 := by
    intro v hv
    have ht := (hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a 0 0 v hv).1
    simpa only [Real.norm_eq_abs,dens,h,Nat.zero_add] using ht
  have hTJ (a : Fin 3) : HasCoordinateWordJetBound 2 (fun _ : R3 => T a) x MT beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (T a) x MT beta (hT a) hb0
  have hDensT (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => dens a y • T a) x (4*Cm*MT*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul 2 (dens a) (fun _ : R3 => T a) (hdensS a) contDiff_const
      x (Cm*eps) MT beta 0 0 (mul_nonneg hCm.le heps) hMT hb0 (hdensj a) (hTJ a)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hDensSum := hasCoordinateWordJetBound_sum 2 (fun a y => dens a y • T a)
    (fun a => (hdensS a).smul contDiff_const) x (4*Cm*MT*eps) beta 0 hDensT
  have hDensSum' : HasCoordinateWordJetBound 2 (fun y => ∑ a : Fin 3, dens a y • T a)
      x (12*Cm*MT*eps) beta 0 := by
    convert hDensSum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have h0 := hasCoordinateWordJetBound_sub 2 (fun y => (A y-Div y) • ((2 : ℝ) • I))
    (fun y => mui y • ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y)))
    ((hAS.sub hDivS).smul contDiff_const) (hmuiS.smul hYSumS) x
    (8*(Ca+Cd)*eps) (192*M^2*CK*eps) beta 0 hADIj hAdjj
  have h1 := hasCoordinateWordJetBound_add 2
    (fun y => (A y-Div y) • ((2 : ℝ) • I)-mui y • ∑ j : Fin 3, (Y j y+ContinuousLinearMap.adjoint (Y j y)))
    (fun y => ∑ a : Fin 3, dens a y • T a)
    (((hAS.sub hDivS).smul contDiff_const).sub (hmuiS.smul hYSumS))
    (ContDiff.sum fun a _ => (hdensS a).smul contDiff_const) x
    (8*(Ca+Cd)*eps+192*M^2*CK*eps) (12*Cm*MT*eps) beta 0 h0 hDensSum'
  change HasCoordinateWordJetBound 2
    (nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
    ((8*(Ca+Cd)*eps+192*M^2*CK*eps)+12*Cm*MT*eps) beta 0 at h1
  have hconst : (8*(Ca+Cd)*eps+192*M^2*CK*eps)+12*Cm*MT*eps = (C-1)*eps := by dsimp only [C]; ring
  exact (h1 w hw).trans (by
    rw [hconst]
    simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C-1 ≤ C by linarith) heps) (pow_nonneg hb0 w.length))


theorem exists_nativeW_coordinate_word_uniform_half_threehalf_form_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ w : List (Fin 3), w.length ≤ 2 →
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪coordinateFieldWordPartial w
          (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
          (coreWeightOperator hO hD (besselWeight 2) F x), G x⟫_ℝ| ≤
        ((C * eps) * beta^w.length) *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨Cs,hCs,hSBound⟩ := exists_nativeWSymmetricHalfAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨Cw,hCw,hWBound⟩ := exists_nativeW_coordinate_word_uniform_threehalf_half_form_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  let C : ℝ := 1+Cs+Cw
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw F G
  let A := coordinateFieldWordPartial w (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
  let S := coordinateFieldWordPartial w (nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
  let UF := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let UG := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let VG := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x
  let a : ℝ := ⟪A (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ
  let b : ℝ := ⟪F x,A (coreWeightOperator hO hD (besselWeight 2) G x)⟫_ℝ
  let s : ℝ := ⟪S UF,UG⟫_ℝ
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hUG : (UG,VG) ∈ sphereBesselGraph hO hD 1 := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) G x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x) k,smul_smul,
      ← SectionFiveErrorForms.besselWeight_add]
    norm_num
  have hi : inverseDegreeMultiplier hO hD VG = UG := inverseDegreeMultiplier_of_besselGraph hO hD UG VG hUG
  have hnorm : ‖UG‖ ≤ ‖VG‖ := by
    calc
      ‖UG‖ = ‖inverseDegreeMultiplier hO hD VG‖ := by rw [hi]
      _ ≤ ‖inverseDegreeMultiplier hO hD‖*‖VG‖ := (inverseDegreeMultiplier hO hD).le_opNorm VG
      _ ≤ 1*‖VG‖ := mul_le_mul_of_nonneg_right (norm_inverseDegreeMultiplier_le_one hO hD) (norm_nonneg VG)
      _ = ‖VG‖ := one_mul _
  have hSym : a+b=s := coordinateFieldWordPartial_nativeW_symmetric_inner_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR w F G x
  have hS : ‖S‖ ≤ (Cs*eps)*beta^w.length :=
    hSBound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw
  have hs : |s| ≤ ((Cs*eps)*beta^w.length)*‖UF‖*‖VG‖ := by
    have ht : |s| ≤ ((Cs*eps)*beta^w.length)*‖UF‖*‖UG‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        ((S.le_opNorm UF).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg UF))) (norm_nonneg UG))
    exact ht.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hbform : |b| ≤ ((Cw*eps)*beta^w.length)*‖UF‖*‖VG‖ := by
    have ht := hWBound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw G F
    have he : b=⟪A (coreWeightOperator hO hD (besselWeight 2) G x),F x⟫_ℝ := real_inner_comm _ _
    rw [he]
    convert ht using 1 <;> dsimp only [UF,VG] <;> ring
  have hab : a=s-b := by linarith
  calc
    |a| = |s-b| := congrArg abs hab
    _ ≤ |s|+|b| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le s (-b)
    _ ≤ ((Cs*eps)*beta^w.length)*‖UF‖*‖VG‖+((Cw*eps)*beta^w.length)*‖UF‖*‖VG‖ := add_le_add hs hbform
    _ = (((Cs+Cw)*eps)*beta^w.length)*‖UF‖*‖VG‖ := by ring
    _ ≤ ((C*eps)*beta^w.length)*‖UF‖*‖VG‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg VG)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg UF)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb0 w.length)
      apply mul_le_mul_of_nonneg_right _ heps
      dsimp only [C]
      linarith


theorem exists_nativeW_uniform_half_threehalf_form_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ| ≤
        (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta^2) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBound⟩ := exists_nativeW_coordinate_word_uniform_half_threehalf_form_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k F G
  refine ⟨?_,?_,?_⟩
  · rw [nativeW_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hBound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) F G
  · rw [coefficientDerivative_nativeW_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
      (coordinateDirection i) F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd,pow_one] using
      hBound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i] (by simp) F G
  · rw [coefficientDerivative_second_nativeW_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
      (coordinateDirection i) (coordinateDirection k) F x]
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd] using
      hBound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i,k] (by simp) F G

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
