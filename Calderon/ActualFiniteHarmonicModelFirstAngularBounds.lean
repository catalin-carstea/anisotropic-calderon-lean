import Calderon.ActualFiniteHarmonicModelFirstAngularJets
import Calderon.ActualNormalizedPrincipalDensityCoefficientJets
import Calderon.ActualReferenceDDHigherActualCoefficients
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore BoundedAngularShift
  ActualNormalizedSecondModelDefectCoefficients ActualNormalizedSecondModelErrorAssembly
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherActualCoefficients ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityScalarZeroForm ActualNormalizedPrincipalDensityCoefficientJets
  ActualNormalizedSecondDriftWeightedCoefficients ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondMetricDrift ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  NaturalAngularAdjoint SmoothMetricFrame SmoothSphereFields SmoothAngularApplication
  PrincipalCommutator ConformalDepth RadiusProfile ReferenceWeightedApproximation
  CoordinateBootstrapJets MetricOperator ActualHorizontalNormBridge
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
lemma coordinateFieldWordPartial_adjoint
    (B : R3 → SphereL2 →L[ℝ] SphereL2) (hB : ContDiff ℝ ∞ B) (w : List (Fin 3)) :
    coordinateFieldWordPartial w (fun y => ContinuousLinearMap.adjoint (B y)) =
      fun x => ContinuousLinearMap.adjoint (coordinateFieldWordPartial w B x) := by
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] (SphereL2 →L[ℝ] SphereL2) :=
    (ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
      (SphereL2 →L[ℝ] SphereL2)).toLinearIsometry.toContinuousLinearMap
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k)
      (coordinateFieldWordPartial w (fun y => ContinuousLinearMap.adjoint (B y))) =
      fun x => ContinuousLinearMap.adjoint
        (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w B) x)
    rw [ih]
    funext x
    exact ActualReferenceDecomposition.directionalFDeriv_fixed_map J (coordinateFieldWordPartial w B)
      (contDiff_coordinateFieldWordPartial w B hB) (coordinateDirection k) x

lemma nativeHFirstAngularCoefficient_eq_defect_sub_reference
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) :
    nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j =
      fun x => modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x -
        (2 : ℝ) • ∑ a : Fin 3, referenceMetricGramFrame g1 L (lam,x) a j •
          (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a) := by
  funext x
  unfold nativeHFirstAngularCoefficient modelDefectFirstNormalizedCoefficient
    normalizedSecondDriftFirstNormalizedCoefficient
  simp only [Fin.sum_univ_three]
  module

theorem exists_modelDefectFirstNormalizedCoefficient_uniform_coordinate_word_smallness (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x‖ ≤
          (C * eps / beta) * beta^w.length := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 3
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 3
  obtain ⟨CK,hCK,hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 2 (by norm_num)
  obtain ⟨CJ,hCJ,hDrift⟩ := exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 2
  let S (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a
  let MS : ℝ := 1 + ∑ a : Fin 3, ‖S a‖
  let Dm : ℝ := 6*(2 : ℝ)^3*M
  let Ca : ℝ := scalarAdjointFirstCoordinateJetConstant 2*Cr*M^3
  let CV : ℝ := 1 + 4*Ca + 2*CK + 12*Dm*MS + 8*CJ
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMS : 1 ≤ MS := by
    dsimp only [MS]
    have hh : 0 ≤ ∑ a : Fin 3, ‖S a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hMS0 : 0 ≤ MS := le_trans zero_le_one hMS
  have hDm : 0 ≤ Dm := by dsimp only [Dm]; positivity
  have hCa : 0 ≤ Ca := by
    dsimp only [Ca,scalarAdjointFirstCoordinateJetConstant,
      weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]
    positivity
  have hCV : 0 < CV := by dsimp only [CV]; positivity
  have hS (a : Fin 3) : ‖S a‖ ≤ MS := by
    have hh : ‖S a‖ ≤ ∑ b : Fin 3, ‖S b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg (S b)) (Finset.mem_univ a)
    dsimp only [MS]
    linarith
  refine ⟨CV,hCV,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j w hw
  let r : ℝ := referenceRadius δ R p L x
  let Rate : ℝ := eps/beta
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have hRate : 0 ≤ Rate := div_nonneg heps hb0
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ Rate := (le_div_iff₀ hbpos).2 (by nlinarith)
  have hRate1 : Rate ≤ 1 := (div_le_iff₀ hbpos).2 (by linarith)
  have hrb1 : r*beta ≤ 1 := hrb.trans hRate1
  have hr1 : r ≤ 1 := by nlinarith
  have hepsr1 : eps*r ≤ 1 := by
    have ht := mul_le_mul heps1 hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using ht
  have hepsr : eps*r ≤ Rate := (le_div_iff₀ hbpos).2 (by
    have ht := mul_le_mul_of_nonneg_left hrb1 heps
    nlinarith)
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let A : R3 → ℝ := fun y => adjointFirstCoefficient coordinateDirection
    (fun z => referenceDensityFamily g1 L (lam,z)) (actualPrincipalMatrix g1 L lam δ R p h) y j
  let B : R3 → SphereL2 →L[ℝ] SphereL2 :=
    referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  let Badj : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ContinuousLinearMap.adjoint (B y)
  let m (a : Fin 3) : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam h a j
  let J : R3 → SphereL2 →L[ℝ] SphereL2 :=
    normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j
  let I : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  have hAS : ContDiff ℝ ∞ A :=
    contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hBS : ContDiff ℝ ∞ B :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hBadjS : ContDiff ℝ ∞ Badj := contDiff_angularAdjoint B hBS
  have hmS (a : Fin 3) : ContDiff ℝ ∞ (m a) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hJS : ContDiff ℝ ∞ J :=
    contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR j
  have hAj : HasCoordinateWordJetBound 2 A x (Ca*Rate) beta 0 := by
    intro v hv
    have ht := abs_actualScalarAdjointFirst_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr 2 (by norm_num) hδ hR heps hM hCr.le hepsr1 hb
      (hgeom lam hlam x hx) (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8 v hv j
    calc
      ‖coordinateFieldWordPartial v A x‖ = |coordinateFieldWordPartial v A x| := Real.norm_eq_abs _
      _ ≤ Ca*r*beta^(v.length+1) := by simpa only [A,Ca,r,h] using ht
      _ = Ca*(r*beta)*beta^v.length := by rw [pow_succ]; ring
      _ ≤ (Ca*Rate)*beta^(0+v.length) := by
        simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrb hCa) (pow_nonneg hb0 v.length)
  have hBj : HasCoordinateWordJetBound 2 B x (CK*Rate) beta 0 := by
    intro v hv
    have ht := (hDD lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx
      hb hH8 hsmall v hv).1 j
    simpa only [B,Rate,beta,actualReferenceBeta,Nat.zero_add,mul_div_assoc] using ht
  have hBadjj : HasCoordinateWordJetBound 2 Badj x (CK*Rate) beta 0 := by
    intro v hv
    dsimp only [Badj]
    rw [coordinateFieldWordPartial_adjoint B hBS v]
    exact ((ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
      (SphereL2 →L[ℝ] SphereL2)).norm_map (coordinateFieldWordPartial v B x)).le.trans (hBj v hv)
  have hmj (a : Fin 3) : HasCoordinateWordJetBound 2 (m a) x (Dm*Rate) beta 0 := by
    intro v hv
    have ht := abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps r M 3 (by norm_num) heps hr.le hM0 (hgeom lam hlam x hx).1 hH8 v (by omega) a j
    calc
      ‖coordinateFieldWordPartial v (m a) x‖ = |coordinateFieldWordPartial v (m a) x| := Real.norm_eq_abs _
      _ ≤ Dm*(eps*r) := by simpa only [Dm,m,h,mul_assoc] using ht
      _ ≤ Dm*Rate := mul_le_mul_of_nonneg_left hepsr hDm
      _ ≤ (Dm*Rate)*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using mul_le_mul_of_nonneg_left
          (one_le_pow₀ hb) (mul_nonneg hDm hRate)
  have hjrate : eps/beta^2 ≤ Rate := (div_le_div_iff₀ (sq_pos_of_pos hbpos) hbpos).2 (by
    have hh : 0 ≤ beta^2-beta := by nlinarith
    nlinarith [mul_nonneg heps hh])
  have hJj : HasCoordinateWordJetBound 2 J x (CJ*Rate) beta 0 := by
    intro v hv
    have ht := (hDrift lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall v hv).1 j
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hjrate hCJ.le) (pow_nonneg hb0 v.length)
    exact ht.trans (by simpa only [Rate,beta,actualReferenceBeta,Nat.zero_add,mul_div_assoc] using hscale)
  have hIj : HasCoordinateWordJetBound 2 (fun _ : R3 => I) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 I x 1 beta
      (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hAIj := hasCoordinateWordJetBound_smul 2 A (fun _ : R3 => I) hAS contDiff_const x
    (Ca*Rate) 1 beta 0 0 (mul_nonneg hCa hRate) (by norm_num) hb0 hAj hIj
  have hAIj' : HasCoordinateWordJetBound 2 (fun y => A y • I) x (4*Ca*Rate) beta 0 := by
    simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero,mul_one,mul_assoc] using hAIj
  have hSj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun _ : R3 => S a) x MS beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (S a) x MS beta (hS a) hb0
  have hMixj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => m a y • S a) x
      (4*Dm*MS*Rate) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul 2 (m a) (fun _ : R3 => S a)
      (hmS a) contDiff_const x (Dm*Rate) MS beta 0 0
      (mul_nonneg hDm hRate) hMS0 hb0 (hmj a) (hSj a)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hMixSum := hasCoordinateWordJetBound_sum 2 (fun a y => m a y • S a)
    (fun a => (hmS a).smul contDiff_const) x (4*Dm*MS*Rate) beta 0 hMixj
  have hMixSum' : HasCoordinateWordJetBound 2 (fun y => ∑ a : Fin 3, m a y • S a) x
      (12*Dm*MS*Rate) beta 0 := by
    convert hMixSum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hTwoj : HasCoordinateWordJetBound 2 (fun _ : R3 => (2 : ℝ)) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (2 : ℝ) x 2 beta (by norm_num) hb0
  have hTwoJ := hasCoordinateWordJetBound_smul 2 (fun _ : R3 => (2 : ℝ)) J
    contDiff_const hJS x 2 (CJ*Rate) beta 0 0 (by norm_num) (mul_nonneg hCJ.le hRate) hb0 hTwoj hJj
  have hTwoJ' : HasCoordinateWordJetBound 2 (fun y => (2 : ℝ) • J y) x (8*CJ*Rate) beta 0 := by
    convert hTwoJ using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have h0 := hasCoordinateWordJetBound_sub 2 (fun y => A y • I) B
    (hAS.smul contDiff_const) hBS x (4*Ca*Rate) (CK*Rate) beta 0 hAIj' hBj
  have h1 := hasCoordinateWordJetBound_sub 2 (fun y => A y • I-B y) Badj
    ((hAS.smul contDiff_const).sub hBS) hBadjS x (4*Ca*Rate+CK*Rate)
    (CK*Rate) beta 0 h0 hBadjj
  have hMixS : ContDiff ℝ ∞ (fun y => ∑ a : Fin 3, m a y • S a) :=
    ContDiff.sum (fun a _ => (hmS a).smul contDiff_const)
  have h2 := hasCoordinateWordJetBound_sub 2 (fun y => A y • I-B y-Badj y)
    (fun y => ∑ a : Fin 3, m a y • S a)
    (((hAS.smul contDiff_const).sub hBS).sub hBadjS) hMixS x
    ((4*Ca*Rate+CK*Rate)+CK*Rate) (12*Dm*MS*Rate) beta 0 h1 hMixSum'
  have h3 := hasCoordinateWordJetBound_sub 2
    (fun y => A y • I-B y-Badj y-∑ a : Fin 3, m a y • S a)
    (fun y => (2 : ℝ) • J y)
    ((((hAS.smul contDiff_const).sub hBS).sub hBadjS).sub hMixS)
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul hJS) x
    (((4*Ca*Rate+CK*Rate)+CK*Rate)+12*Dm*MS*Rate) (8*CJ*Rate) beta 0 h2 hTwoJ'
  change HasCoordinateWordJetBound 2
    (modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x
    ((((4*Ca*Rate+CK*Rate)+CK*Rate)+12*Dm*MS*Rate)+8*CJ*Rate) beta 0 at h3
  have hsum : (((4*Ca*Rate+CK*Rate)+CK*Rate)+12*Dm*MS*Rate)+8*CJ*Rate =
      (CV-1)*Rate := by dsimp only [CV]; ring
  have hscale : (((4*Ca*Rate+CK*Rate)+CK*Rate)+12*Dm*MS*Rate)+8*CJ*Rate ≤ CV*eps/beta := by
    rw [hsum]
    calc
      (CV-1)*Rate ≤ CV*Rate := mul_le_mul_of_nonneg_right (by linarith) hRate
      _ = CV*eps/beta := by dsimp only [Rate]; ring
  exact (h3 w hw).trans (by simpa only [Nat.zero_add] using
    mul_le_mul_of_nonneg_right hscale (pow_nonneg hb0 w.length))

theorem exists_nativeHFirstAngularCoefficient_uniform_coordinate_word_bounds (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x‖ ≤
          C * beta^w.length := by
  obtain ⟨CV,hCV,hV⟩ := exists_modelDefectFirstNormalizedCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 3
  let S (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a
  let MS : ℝ := 1+∑ a : Fin 3, ‖S a‖
  let C : ℝ := 1+CV+96*M*MS
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMS : 1 ≤ MS := by
    have hh : 0 ≤ ∑ a : Fin 3, ‖S a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [MS]
    linarith
  have hMS0 : 0 ≤ MS := le_trans zero_le_one hMS
  have hS (a : Fin 3) : ‖S a‖ ≤ MS := by
    have hh : ‖S a‖ ≤ ∑ b : Fin 3, ‖S b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg (S b)) (Finset.mem_univ a)
    dsimp only [MS]
    linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j w hw
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  let E (a : Fin 3) : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a j
  let V : R3 → SphereL2 →L[ℝ] SphereL2 :=
    modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j
  let Ref : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, E a y • S a
  have hES (a : Fin 3) : ContDiff ℝ ∞ (E a) :=
    (contDiff_piLp_apply (p := 2) (i := j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hEj (a : Fin 3) : HasCoordinateWordJetBound 2 (E a) x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx).1.1 v (by omega) a j
    calc
      ‖coordinateFieldWordPartial v (E a) x‖ = |coordinateFieldWordPartial v (E a) x| := Real.norm_eq_abs _
      _ ≤ M := ht
      _ ≤ M*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0
  have hSj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun _ : R3 => S a) x MS beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (S a) x MS beta (hS a) hb0
  have hTermj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => E a y • S a) x
      (4*M*MS) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul 2 (E a) (fun _ : R3 => S a)
      (hES a) contDiff_const x M MS beta 0 0 hM0 hMS0 hb0 (hEj a) (hSj a)
    simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] using ht
  have hRefS : ContDiff ℝ ∞ Ref := ContDiff.sum (fun a _ => (hES a).smul contDiff_const)
  have hRefj := hasCoordinateWordJetBound_sum 2 (fun a y => E a y • S a)
    (fun a => (hES a).smul contDiff_const) x (4*M*MS) beta 0 hTermj
  have hRefj' : HasCoordinateWordJetBound 2 Ref x (12*M*MS) beta 0 := by
    convert hRefj using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hTwoj : HasCoordinateWordJetBound 2 (fun _ : R3 => (2 : ℝ)) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (2 : ℝ) x 2 beta (by norm_num) hb0
  have hTwoRef := hasCoordinateWordJetBound_smul 2 (fun _ : R3 => (2 : ℝ)) Ref
    contDiff_const hRefS x 2 (12*M*MS) beta 0 0 (by norm_num)
      (by positivity) hb0 hTwoj hRefj'
  have hTwoRef' : HasCoordinateWordJetBound 2 (fun y => (2 : ℝ) • Ref y) x
      (96*M*MS) beta 0 := by
    convert hTwoRef using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hVeq : V = fun y => nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j y +
      (2 : ℝ) • Ref y := by
    funext y
    have ht := congrFun (nativeHFirstAngularCoefficient_eq_defect_sub_reference
      hO hD hF g1 g2 hg1 L lam δ R p j) y
    exact (sub_eq_iff_eq_add).mp ht.symm
  have hVS : ContDiff ℝ ∞ V := by
    rw [hVeq]
    exact (contDiff_nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR).add
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul hRefS)
  have hVj : HasCoordinateWordJetBound 2 V x CV beta 0 := by
    intro v hv
    have ht := hV lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j v hv
    have hRate : CV*eps/beta ≤ CV := (div_le_iff₀ hbpos).2
      (mul_le_mul_of_nonneg_left (by linarith : eps ≤ beta) hCV.le)
    exact ht.trans (by simpa only [Nat.zero_add] using
      mul_le_mul_of_nonneg_right hRate (pow_nonneg hb0 v.length))
  have hHj := hasCoordinateWordJetBound_sub 2 V (fun y => (2 : ℝ) • Ref y) hVS
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul hRefS) x CV (96*M*MS) beta 0 hVj hTwoRef'
  change HasCoordinateWordJetBound 2 (fun y =>
    modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j y -
      (2 : ℝ) • ∑ a : Fin 3, referenceMetricGramFrame g1 L (lam,y) a j •
        (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)) x
    (CV+96*M*MS) beta 0 at hHj
  rw [← nativeHFirstAngularCoefficient_eq_defect_sub_reference hO hD hF g1 g2 hg1 L lam δ R p j] at hHj
  have hRate : CV+96*M*MS ≤ C := by dsimp only [C]; linarith
  exact (hHj w hw).trans (by simpa only [Nat.zero_add] using
    mul_le_mul_of_nonneg_right hRate (pow_nonneg hb0 w.length))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
