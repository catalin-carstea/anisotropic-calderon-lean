import Calderon.ActualFiniteHarmonicModelSecondAngularDriftFold
import Calderon.ActualFiniteHarmonicModelSecondBalancedAngularJets
import Calderon.ActualFiniteHarmonicModelMixedZeroScalarJets
import Calderon.ActualFiniteHarmonicModelFirstAngularBounds
import Calderon.ActualNormalizedSecondDriftDefectCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SpectralWeightedGraph ActualReferenceDDHigherSpectralGraphs SphereHarmonic ActualFiniteHarmonicCore BoundedAngularShift BalancedAngularShift ActualNormalizedSphereRotation
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
private abbrev nativeWBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWBoundsFunction
theorem exists_nativeWSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
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
        (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x‖ ≤
          (C * eps) * beta^w.length := by
  classical
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 4
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 4
  obtain ⟨CK,hCK,hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 3 (by norm_num)
  obtain ⟨Cm,hCm,hMixed⟩ := exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness
    g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CJ,hCJ,hDrift⟩ := exists_normalizedSecondDriftDefectNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 2
  let I : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  let Id : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2
  let SD (a : Fin 3) := (balancedDerivative hF hO hD a).comp I
  let SP (a : Fin 3) := (balancedDerivative hF hO hD a).comp (Id-(2 : ℝ) • I)
  let SPR (a : Fin 3) := (balancedRaising hF hO hD a).comp (Id-I)
  let SC (a b c : Fin 3) := (normalizedRotation hO hD b c).comp
    ((balancedDerivative hF hO hD a).comp (Id-I))
  let SCR (a b c : Fin 3) := (balancedRaising hF hO hD a).comp (normalizedRotation hO hD b c)
  let SU (a b : Fin 3) := (balancedDerivative hF hO hD b).comp
    ((balancedDerivative hF hO hD a).comp (Id-I))
  let SUR (a b : Fin 3) := (balancedRaising hF hO hD a).comp
    ((balancedRaising hF hO hD b).comp (Id+I))
  let MD : ℝ := 1+∑ a : Fin 3, ‖SD a‖
  let MP : ℝ := 1+∑ a : Fin 3, (‖SP a‖+‖SPR a‖)
  let MC : ℝ := 1+∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (‖SC a b c‖+‖SCR a b c‖)
  let MU : ℝ := 1+∑ a : Fin 3, ∑ b : Fin 3, (‖SU a b‖+‖SUR a b‖)
  let Ca : ℝ := scalarAdjointZeroCoordinateJetConstant 2*Cr*M^3
  let C : ℝ := 1+4*Ca+384*M^2*CK+2*CK+12*Cm*MD+24*Cm*MP+216*Cm*MC+72*Cm*MU+CJ
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hCa : 0 ≤ Ca := by
    dsimp only [Ca,scalarAdjointZeroCoordinateJetConstant,
      weightedNormalizedPrincipalCoordinateJetConstant,normalizedPrincipalCoordinateJetConstant]
    positivity
  have hMD : 0 ≤ MD := by dsimp only [MD]; positivity
  have hMP : 0 ≤ MP := by dsimp only [MP]; positivity
  have hMC : 0 ≤ MC := by dsimp only [MC]; positivity
  have hMU : 0 ≤ MU := by dsimp only [MU]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hSD (a : Fin 3) : ‖SD a‖ ≤ MD := by
    have ht := Finset.single_le_sum (fun b _ => norm_nonneg (SD b)) (Finset.mem_univ a)
    dsimp only [MD]
    linarith
  have hSPpair (a : Fin 3) : ‖SP a‖+‖SPR a‖ ≤ MP := by
    have ht := Finset.single_le_sum (fun b _ => add_nonneg (norm_nonneg (SP b)) (norm_nonneg (SPR b)))
      (Finset.mem_univ a)
    dsimp only [MP]
    linarith
  have hSCpair (a b c : Fin 3) : ‖SC a b c‖+‖SCR a b c‖ ≤ MC := by
    have h1 : ‖SC a b c‖+‖SCR a b c‖ ≤ ∑ t : Fin 3, (‖SC a b t‖+‖SCR a b t‖) :=
      Finset.single_le_sum (fun t _ => add_nonneg (norm_nonneg (SC a b t)) (norm_nonneg (SCR a b t)))
        (Finset.mem_univ c)
    have h2 : (∑ t : Fin 3, (‖SC a b t‖+‖SCR a b t‖)) ≤
        ∑ s : Fin 3, ∑ t : Fin 3, (‖SC a s t‖+‖SCR a s t‖) :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg
        (fun t _ => add_nonneg (norm_nonneg (SC a s t)) (norm_nonneg (SCR a s t)))) (Finset.mem_univ b)
    have h3 : (∑ s : Fin 3, ∑ t : Fin 3, (‖SC a s t‖+‖SCR a s t‖)) ≤
        ∑ r : Fin 3, ∑ s : Fin 3, ∑ t : Fin 3, (‖SC r s t‖+‖SCR r s t‖) :=
      Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
        (fun t _ => add_nonneg (norm_nonneg (SC r s t)) (norm_nonneg (SCR r s t))))) (Finset.mem_univ a)
    dsimp only [MC]
    linarith
  have hSUpair (a b : Fin 3) : ‖SU a b‖+‖SUR a b‖ ≤ MU := by
    have h1 : ‖SU a b‖+‖SUR a b‖ ≤ ∑ t : Fin 3, (‖SU a t‖+‖SUR a t‖) :=
      Finset.single_le_sum (fun t _ => add_nonneg (norm_nonneg (SU a t)) (norm_nonneg (SUR a t))) (Finset.mem_univ b)
    have h2 : (∑ t : Fin 3, (‖SU a t‖+‖SUR a t‖)) ≤
        ∑ s : Fin 3, ∑ t : Fin 3, (‖SU s t‖+‖SUR s t‖) :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg
        (fun t _ => add_nonneg (norm_nonneg (SU s t)) (norm_nonneg (SUR s t)))) (Finset.mem_univ a)
    dsimp only [MU]
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
  let B0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  let BA (j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ContinuousLinearMap.adjoint (B j y)
  let Y (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (B j)
  let Z := normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p
  have hmuS : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmuiS : ContDiff ℝ ∞ mui :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hAS : ContDiff ℝ ∞ A := contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hBS (j : Fin 3) : ContDiff ℝ ∞ (B j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hB0S : ContDiff ℝ ∞ B0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p hδ hR h hh
  have hBAS (j : Fin 3) : ContDiff ℝ ∞ (BA j) := contDiff_angularAdjoint (B j) (hBS j)
  have hYS (j : Fin 3) : ContDiff ℝ ∞ (Y j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hmuS.smul (hBAS j))
  have hZS : ContDiff ℝ ∞ Z :=
    contDiff_normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR
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
  have hB0j : HasCoordinateWordJetBound 2 B0 x (CK*eps) beta 0 := by
    intro v hv
    have ht := (hDD lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx
      hb hH8 hsmall v (by omega)).2
    simpa only [B0,beta,actualReferenceBeta,Nat.zero_add] using ht
  have hB0Aj : HasCoordinateWordJetBound 2 (fun y => ContinuousLinearMap.adjoint (B0 y)) x (CK*eps) beta 0 := by
    intro v hv
    rw [coordinateFieldWordPartial_adjoint B0 hB0S v]
    exact ((ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
      (SphereL2 →L[ℝ] SphereL2)).norm_map (coordinateFieldWordPartial v B0 x)).le.trans (hB0j v hv)
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
  have hIj : HasCoordinateWordJetBound 2 (fun _ : R3 => I) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 I x 1 beta (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hI2 : ‖I.comp I‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le I I).trans
      (by nlinarith [norm_inverseDegreeMultiplier_le_one hO hD,norm_nonneg I])
  have hI2j : HasCoordinateWordJetBound 2 (fun _ : R3 => I.comp I) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 _ x 1 beta hI2 hb0
  have hAI := hasCoordinateWordJetBound_smul 2 A (fun _ : R3 => I.comp I) hAS contDiff_const
    x (Ca*eps) 1 beta 0 0 (mul_nonneg hCa heps) (by norm_num) hb0 hAj hI2j
  have hAIj : HasCoordinateWordJetBound 2 (fun y => A y • I.comp I) x (4*Ca*eps) beta 0 := by
    simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero,mul_one,mul_assoc] using hAI
  have hYIj (j : Fin 3) : HasCoordinateWordJetBound 2 (fun y => (Y j y).comp I) x (32*M*CK*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_clm_comp 2 (Y j) (fun _ : R3 => I) (hYS j) contDiff_const
      x (8*M*CK*eps) 1 beta 0 0 (by positivity) (by norm_num) hb0 (hYj j) hIj
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hYIS : ContDiff ℝ ∞ (fun y : R3 => ∑ j : Fin 3, (Y j y).comp I) :=
    ContDiff.sum (fun j _ => (hYS j).clm_comp contDiff_const)
  have hYISum := hasCoordinateWordJetBound_sum 2 (fun j y => (Y j y).comp I)
    (fun j => (hYS j).clm_comp contDiff_const) x (32*M*CK*eps) beta 0 hYIj
  have hYISum' : HasCoordinateWordJetBound 2 (fun y => ∑ j : Fin 3, (Y j y).comp I)
      x (96*M*CK*eps) beta 0 := by
    convert hYISum using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hAdj := hasCoordinateWordJetBound_smul 2 mui (fun y => ∑ j : Fin 3, (Y j y).comp I)
    hmuiS hYIS x M (96*M*CK*eps) beta 0 0 hM0 (by positivity) hb0 hmuij hYISum'
  have hAdjj : HasCoordinateWordJetBound 2 (fun y => mui y • ∑ j : Fin 3, (Y j y).comp I)
      x (384*M^2*CK*eps) beta 0 := by
    convert hAdj using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hK0j := hasCoordinateWordJetBound_sub 2 (fun y => ContinuousLinearMap.adjoint (B0 y)) B0
    (contDiff_angularAdjoint B0 hB0S) hB0S x (CK*eps) (CK*eps) beta 0 hB0Aj hB0j
  have hZj : HasCoordinateWordJetBound 2 Z x (CJ*eps) beta 0 := by
    intro v hv
    have ht := (hDrift lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall v hv).2
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRateeps hCJ.le) (pow_nonneg hb0 v.length)
    exact ht.trans (by simpa only [Z,beta,actualReferenceBeta,Nat.zero_add,Rate,mul_div_assoc] using hscale)
  let dens (a : Fin 3) := physicalMixedDensityCorrection g1 L lam h a
  let prof (a : Fin 3) := physicalMixedProfileCoefficient g1 L lam δ R p h a
  let conn (a b c : Fin 3) := physicalMixedConnectionCoefficient g1 L lam h a b c
  let pure (a b : Fin 3) := physicalPureAngularCoefficient g1 L lam δ R p h a b
  have hdensS (a : Fin 3) : ContDiff ℝ ∞ (dens a) :=
    contDiff_physicalMixedDensityCorrection g1 hg1 L lam h hhe a
  have hprofS (a : Fin 3) : ContDiff ℝ ∞ (prof a) :=
    contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhe a
  have hconnS (a b c : Fin 3) : ContDiff ℝ ∞ (conn a b c) :=
    contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhe a b c
  have hpureS (a b : Fin 3) : ContDiff ℝ ∞ (pure a b) :=
    contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhe a b
  have hMixedj (a b c : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ 2) :=
    hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a b c v hv
  have hdensj (a : Fin 3) : HasCoordinateWordJetBound 2 (dens a) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,dens,h,Nat.zero_add] using (hMixedj a 0 0 v hv).1
  have hprofj (a : Fin 3) : HasCoordinateWordJetBound 2 (prof a) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,prof,h,Nat.zero_add] using (hMixedj a 0 0 v hv).2.1
  have hconnj (a b c : Fin 3) : HasCoordinateWordJetBound 2 (conn a b c) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,conn,h,Nat.zero_add] using (hMixedj a b c v hv).2.2.1
  have hpurej (a b : Fin 3) : HasCoordinateWordJetBound 2 (pure a b) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,pure,h,Nat.zero_add] using (hMixedj a b 0 v hv).2.2.2
  have hScalarFixed (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (S : SphereL2 →L[ℝ] SphereL2)
      (MS : ℝ) (hMS : 0 ≤ MS) (hS : ‖S‖ ≤ MS)
      (hfjet : HasCoordinateWordJetBound 2 f x (Cm*eps) beta 0) :
      HasCoordinateWordJetBound 2 (fun y => f y • S) x (4*Cm*MS*eps) beta 0 := by
    have hSj := hasCoordinateWordJetBound_const_normed 2 S x MS beta hS hb0
    have ht := hasCoordinateWordJetBound_smul 2 f (fun _ : R3 => S) hf contDiff_const
      x (Cm*eps) MS beta 0 0 (mul_nonneg hCm.le heps) hMS hb0 hfjet hSj
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hDj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => dens a y • SD a)
      x (4*Cm*MD*eps) beta 0 :=
    hScalarFixed (fun y => dens a y) (hdensS a) (SD a) MD hMD
      (hSD a) (hdensj a)
  let FD : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, dens a y • SD a
  have hFDS : ContDiff ℝ ∞ FD :=
    ContDiff.sum (fun a _ => (hdensS a).smul contDiff_const)
  have hDsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, dens a y • SD a) x (12*Cm*MD*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => dens a y • SD a)
      (fun a => (hdensS a).smul contDiff_const) x (4*Cm*MD*eps) beta 0
      (fun a => hDj a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hPj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => prof a y • SP a)
      x (4*Cm*MP*eps) beta 0 :=
    hScalarFixed (fun y => prof a y) (hprofS a) (SP a) MP hMP
      (by have ht := hSPpair a; have hn := norm_nonneg (SPR a); linarith) (hprofj a)
  let FP : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, prof a y • SP a
  have hFPS : ContDiff ℝ ∞ FP :=
    ContDiff.sum (fun a _ => (hprofS a).smul contDiff_const)
  have hPsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, prof a y • SP a) x (12*Cm*MP*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => prof a y • SP a)
      (fun a => (hprofS a).smul contDiff_const) x (4*Cm*MP*eps) beta 0
      (fun a => hPj a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hPRj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => prof a y • SPR a)
      x (4*Cm*MP*eps) beta 0 :=
    hScalarFixed (fun y => prof a y) (hprofS a) (SPR a) MP hMP
      (by have ht := hSPpair a; have hn := norm_nonneg (SP a); linarith) (hprofj a)
  let FPR : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, prof a y • SPR a
  have hFPRS : ContDiff ℝ ∞ FPR :=
    ContDiff.sum (fun a _ => (hprofS a).smul contDiff_const)
  have hPRsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, prof a y • SPR a) x (12*Cm*MP*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => prof a y • SPR a)
      (fun a => (hprofS a).smul contDiff_const) x (4*Cm*MP*eps) beta 0
      (fun a => hPRj a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCj (a b c : Fin 3) : HasCoordinateWordJetBound 2 (fun y => -conn a b c y • SC a b c)
      x (4*Cm*MC*eps) beta 0 :=
    hScalarFixed (fun y => -conn a b c y) (hconnS a b c).neg (SC a b c) MC hMC
      (by have ht := hSCpair a b c; have hn := norm_nonneg (SCR a b c); linarith) (hasCoordinateWordJetBound_neg 2 (conn a b c) (hconnS a b c) x (Cm*eps) beta 0 (hconnj a b c))
  let FC : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, -conn a b c y • SC a b c
  have hFCS : ContDiff ℝ ∞ FC :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => ContDiff.sum (fun c _ => (hconnS a b c).neg.smul contDiff_const)))
  have hCsum2 (a b : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ c : Fin 3, -conn a b c y • SC a b c) x (12*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun c y => -conn a b c y • SC a b c)
      (fun c => (hconnS a b c).neg.smul contDiff_const) x (4*Cm*MC*eps) beta 0
      (fun c => hCj a b c)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, ∑ c : Fin 3, -conn a b c y • SC a b c) x (36*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b y => ∑ c : Fin 3, -conn a b c y • SC a b c)
      (fun b => ContDiff.sum (fun c _ => (hconnS a b c).neg.smul contDiff_const)) x (12*Cm*MC*eps) beta 0
      (fun b => hCsum2 a b)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, -conn a b c y • SC a b c) x (108*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => ∑ b : Fin 3, ∑ c : Fin 3, -conn a b c y • SC a b c)
      (fun a => ContDiff.sum (fun b _ => ContDiff.sum (fun c _ => (hconnS a b c).neg.smul contDiff_const))) x (36*Cm*MC*eps) beta 0
      (fun a => hCsum1 a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCRj (a b c : Fin 3) : HasCoordinateWordJetBound 2 (fun y => conn a b c y • SCR a b c)
      x (4*Cm*MC*eps) beta 0 :=
    hScalarFixed (fun y => conn a b c y) (hconnS a b c) (SCR a b c) MC hMC
      (by have ht := hSCpair a b c; have hn := norm_nonneg (SC a b c); linarith) (hconnj a b c)
  let FCR : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SCR a b c
  have hFCRS : ContDiff ℝ ∞ FCR :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const)))
  have hCRsum2 (a b : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ c : Fin 3, conn a b c y • SCR a b c) x (12*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun c y => conn a b c y • SCR a b c)
      (fun c => (hconnS a b c).smul contDiff_const) x (4*Cm*MC*eps) beta 0
      (fun c => hCRj a b c)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCRsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SCR a b c) x (36*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b y => ∑ c : Fin 3, conn a b c y • SCR a b c)
      (fun b => ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const)) x (12*Cm*MC*eps) beta 0
      (fun b => hCRsum2 a b)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hCRsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SCR a b c) x (108*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SCR a b c)
      (fun a => ContDiff.sum (fun b _ => ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const))) x (36*Cm*MC*eps) beta 0
      (fun a => hCRsum1 a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hUj (a b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => pure a b y • SU a b)
      x (4*Cm*MU*eps) beta 0 :=
    hScalarFixed (fun y => pure a b y) (hpureS a b) (SU a b) MU hMU
      (by have ht := hSUpair a b; have hn := norm_nonneg (SUR a b); linarith) (hpurej a b)
  let FU : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, ∑ b : Fin 3, pure a b y • SU a b
  have hFUS : ContDiff ℝ ∞ FU :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const))
  have hUsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, pure a b y • SU a b) x (12*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b y => pure a b y • SU a b)
      (fun b => (hpureS a b).smul contDiff_const) x (4*Cm*MU*eps) beta 0
      (fun b => hUj a b)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hUsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, ∑ b : Fin 3, pure a b y • SU a b) x (36*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => ∑ b : Fin 3, pure a b y • SU a b)
      (fun a => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const)) x (12*Cm*MU*eps) beta 0
      (fun a => hUsum1 a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hURj (a b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => pure a b y • SUR a b)
      x (4*Cm*MU*eps) beta 0 :=
    hScalarFixed (fun y => pure a b y) (hpureS a b) (SUR a b) MU hMU
      (by have ht := hSUpair a b; have hn := norm_nonneg (SU a b); linarith) (hpurej a b)
  let FUR : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, ∑ b : Fin 3, pure a b y • SUR a b
  have hFURS : ContDiff ℝ ∞ FUR :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const))
  have hURsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, pure a b y • SUR a b) x (12*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b y => pure a b y • SUR a b)
      (fun b => (hpureS a b).smul contDiff_const) x (4*Cm*MU*eps) beta 0
      (fun b => hURj a b)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hURsum0 : HasCoordinateWordJetBound 2
      (fun y => ∑ a : Fin 3, ∑ b : Fin 3, pure a b y • SUR a b) x (36*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => ∑ b : Fin 3, pure a b y • SUR a b)
      (fun a => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const)) x (12*Cm*MU*eps) beta 0
      (fun a => hURsum1 a)
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  let FA : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => A y • I.comp I
  let FY : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => mui y • ∑ j : Fin 3, (Y j y).comp I
  let FK : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ContinuousLinearMap.adjoint (B0 y)-B0 y
  have hFAS : ContDiff ℝ ∞ FA := hAS.smul contDiff_const
  have hFYS : ContDiff ℝ ∞ FY := hmuiS.smul hYIS
  have hFKS : ContDiff ℝ ∞ FK := (contDiff_angularAdjoint B0 hB0S).sub hB0S
  have hFPj := hasCoordinateWordJetBound_sub 2 FP FPR hFPS hFPRS x
    (12*Cm*MP*eps) (12*Cm*MP*eps) beta 0 hPsum0 hPRsum0
  have hFCj := hasCoordinateWordJetBound_sub 2 FC FCR hFCS hFCRS x
    (108*Cm*MC*eps) (108*Cm*MC*eps) beta 0 hCsum0 hCRsum0
  have hFUj := hasCoordinateWordJetBound_sub 2 FU FUR hFUS hFURS x
    (36*Cm*MU*eps) (36*Cm*MU*eps) beta 0 hUsum0 hURsum0
  have h0 := hasCoordinateWordJetBound_sub 2 FA FY hFAS hFYS x
    (4*Ca*eps) (384*M^2*CK*eps) beta 0 hAIj hAdjj
  have h1 := hasCoordinateWordJetBound_add 2 (fun y => FA y-FY y) FK (hFAS.sub hFYS) hFKS x
    (4*Ca*eps+384*M^2*CK*eps) (CK*eps+CK*eps) beta 0 h0 hK0j
  have h2 := hasCoordinateWordJetBound_add 2 (fun y => FA y-FY y+FK y) FD
    ((hFAS.sub hFYS).add hFKS) hFDS x
    ((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps)) (12*Cm*MD*eps) beta 0 h1 hDsum0
  have h3 := hasCoordinateWordJetBound_add 2 (fun y => FA y-FY y+FK y+FD y) (fun y => FP y-FPR y)
    (((hFAS.sub hFYS).add hFKS).add hFDS) (hFPS.sub hFPRS) x
    (((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps))+12*Cm*MD*eps)
    (12*Cm*MP*eps+12*Cm*MP*eps) beta 0 h2 hFPj
  have h4 := hasCoordinateWordJetBound_add 2 (fun y => FA y-FY y+FK y+FD y+(FP y-FPR y)) (fun y => FC y-FCR y)
    ((((hFAS.sub hFYS).add hFKS).add hFDS).add (hFPS.sub hFPRS)) (hFCS.sub hFCRS) x
    ((((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps))+12*Cm*MD*eps)+(12*Cm*MP*eps+12*Cm*MP*eps))
    (108*Cm*MC*eps+108*Cm*MC*eps) beta 0 h3 hFCj
  have h5 := hasCoordinateWordJetBound_add 2
    (fun y => FA y-FY y+FK y+FD y+(FP y-FPR y)+(FC y-FCR y)) (fun y => FU y-FUR y)
    (((((hFAS.sub hFYS).add hFKS).add hFDS).add (hFPS.sub hFPRS)).add (hFCS.sub hFCRS)) (hFUS.sub hFURS) x
    (((((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps))+12*Cm*MD*eps)+(12*Cm*MP*eps+12*Cm*MP*eps))+
      (108*Cm*MC*eps+108*Cm*MC*eps)) (36*Cm*MU*eps+36*Cm*MU*eps) beta 0 h4 hFUj
  have h6 := hasCoordinateWordJetBound_add 2
    (fun y => FA y-FY y+FK y+FD y+(FP y-FPR y)+(FC y-FCR y)+(FU y-FUR y)) Z
    ((((((hFAS.sub hFYS).add hFKS).add hFDS).add (hFPS.sub hFPRS)).add (hFCS.sub hFCRS)).add (hFUS.sub hFURS)) hZS x
    ((((((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps))+12*Cm*MD*eps)+(12*Cm*MP*eps+12*Cm*MP*eps))+
      (108*Cm*MC*eps+108*Cm*MC*eps))+(36*Cm*MU*eps+36*Cm*MU*eps)) (CJ*eps) beta 0 h5 hZj
  have hfield : (fun y => FA y-FY y+FK y+FD y+(FP y-FPR y)+(FC y-FCR y)+(FU y-FUR y)+Z y) =
      nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p := by
    rw [nativeWSecondBalancedAngularCoefficient_eq_full_zeroDrift hO hD hF g1 g2 hg1 L lam δ R p]
  rw [hfield] at h6
  have hconst : ((((((4*Ca*eps+384*M^2*CK*eps)+(CK*eps+CK*eps))+12*Cm*MD*eps)+
      (12*Cm*MP*eps+12*Cm*MP*eps))+(108*Cm*MC*eps+108*Cm*MC*eps))+
      (36*Cm*MU*eps+36*Cm*MU*eps))+CJ*eps = (C-1)*eps := by dsimp only [C]; ring
  exact (h6 w hw).trans (by
    rw [hconst]
    simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C-1 ≤ C by linarith) heps) (pow_nonneg hb0 w.length))


theorem exists_nativeW_coordinate_word_uniform_threehalf_half_form_bound
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
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeWSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw F G
  rw [coordinateFieldWordPartial_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR w F G x]
  let A := coordinateFieldWordPartial w (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
  let U := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have hA : ‖A‖ ≤ (C*eps)*beta^w.length :=
    hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))


theorem exists_nativeW_uniform_threehalf_half_form_bound
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
        (C * eps) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta^2) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeWSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k F G
  let WB := nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let U := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have h0 : ‖WB x‖ ≤ C*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp)
  have h1 : ‖directionalFDeriv (coordinateDirection i) WB x‖ ≤ (C*eps)*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd,pow_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i] (by simp)
  have h2 : ‖directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection k) WB) x‖ ≤ (C*eps)*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i,k] (by simp)
  have hform (A : SphereL2 →L[ℝ] SphereL2) (B : ℝ) (hA : ‖A‖ ≤ B) :
      |⟪A U,V⟫_ℝ| ≤ B*‖U‖*‖V‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))
  refine ⟨?_,?_,?_⟩
  · rw [nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F G x]
    exact hform (WB x) (C*eps) h0
  · rw [coefficientDerivative_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i F G x]
    exact hform (directionalFDeriv (coordinateDirection i) WB x) ((C*eps)*beta) h1
  · rw [coefficientDerivative_second_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i k F G x]
    exact hform (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) WB) x) ((C*eps)*beta^2) h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
