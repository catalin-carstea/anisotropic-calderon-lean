import Calderon.ActualFiniteHarmonicModelZeroAngularJets
import Calderon.ActualFiniteHarmonicModelMixedZeroScalarJets
import Calderon.ActualReferenceDDHigherActualCoefficients
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelDefectCoefficients
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection SmoothSphereFields
  SmoothAngularApplication
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherActualCoefficients
  ActualHorizontalNormBridge CoordinateBootstrapJets ReferenceWeightedApproximation MetricOperator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeCSecondBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCSecondBoundsFunction
theorem exists_nativeCSecondAngularCoefficient_uniform_coordinate_word_smallness
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
        (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x‖ ≤
          (C * eps) * beta^w.length := by
  classical
  obtain ⟨CK, hCK, hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 2 (by norm_num)
  obtain ⟨Cm, hCm, hMixed⟩ := exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness
    g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CJ, hCJ, hDrift⟩ := exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 2
  let I : SphereL2 →L[ℝ] SphereL2 := inverseDegreeMultiplier hO hD
  let Id : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2
  let SP (a : Fin 3) := (normalizedRaising hF hO hD a).comp (Id-I)
  let SC (a b c : Fin 3) := (normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c)
  let SU (a b : Fin 3) := (normalizedRaising hF hO hD a).comp
    ((normalizedRaising hF hO hD b).comp (Id+I))
  let MP : ℝ := 1+∑ a : Fin 3, ‖SP a‖
  let MC : ℝ := 1+∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ‖SC a b c‖
  let MU : ℝ := 1+∑ a : Fin 3, ∑ b : Fin 3, ‖SU a b‖
  let C : ℝ := 1+CK+CJ+12*Cm*MP+108*Cm*MC+36*Cm*MU
  have hMP : 0 ≤ MP := by dsimp only [MP]; positivity
  have hMC : 0 ≤ MC := by dsimp only [MC]; positivity
  have hMU : 0 ≤ MU := by dsimp only [MU]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hSP (a : Fin 3) : ‖SP a‖ ≤ MP := by
    have ht := Finset.single_le_sum (fun b _ => norm_nonneg (SP b)) (Finset.mem_univ a)
    dsimp only [MP]
    linarith
  have hSC (a b c : Fin 3) : ‖SC a b c‖ ≤ MC := by
    have h1 : ‖SC a b c‖ ≤ ∑ t : Fin 3, ‖SC a b t‖ :=
      Finset.single_le_sum (fun t _ => norm_nonneg (SC a b t)) (Finset.mem_univ c)
    have h2 : (∑ t : Fin 3, ‖SC a b t‖) ≤ ∑ s : Fin 3, ∑ t : Fin 3, ‖SC a s t‖ :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun t _ => norm_nonneg (SC a s t)))
        (Finset.mem_univ b)
    have h3 : (∑ s : Fin 3, ∑ t : Fin 3, ‖SC a s t‖) ≤
        ∑ r : Fin 3, ∑ s : Fin 3, ∑ t : Fin 3, ‖SC r s t‖ :=
      Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun s _ =>
        Finset.sum_nonneg (fun t _ => norm_nonneg (SC r s t)))) (Finset.mem_univ a)
    dsimp only [MC]
    linarith
  have hSU (a b : Fin 3) : ‖SU a b‖ ≤ MU := by
    have h1 : ‖SU a b‖ ≤ ∑ t : Fin 3, ‖SU a t‖ :=
      Finset.single_le_sum (fun t _ => norm_nonneg (SU a t)) (Finset.mem_univ b)
    have h2 : (∑ t : Fin 3, ‖SU a t‖) ≤ ∑ s : Fin 3, ∑ t : Fin 3, ‖SU s t‖ :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun t _ => norm_nonneg (SU s t)))
        (Finset.mem_univ a)
    dsimp only [MU]
    linarith
  refine ⟨C, hC, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhe (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0S : ContDiff ℝ ∞ K0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p hδ hR h hh
  have hK0j : HasCoordinateWordJetBound 2 K0 x (CK*eps) beta 0 := by
    intro v hv
    have ht := (hDD lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx hb hH8 hsmall v hv).2
    simpa only [K0, h, beta, actualReferenceBeta, Nat.zero_add] using ht
  let J0 := normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p
  have hJ0S : ContDiff ℝ ∞ J0 :=
    contDiff_normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hJscale : CJ*eps/beta ≤ CJ*eps := by
    apply (div_le_iff₀ hbpos).mpr
    have hn := mul_nonneg hCJ.le heps
    nlinarith
  have hJ0j : HasCoordinateWordJetBound 2 J0 x (CJ*eps) beta 0 := by
    intro v hv
    have ht := (hDrift lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall v hv).2
    have hs := mul_le_mul_of_nonneg_right hJscale (pow_nonneg hb0 v.length)
    exact ht.trans (by simpa only [J0, beta, actualReferenceBeta, Nat.zero_add] using hs)
  let prof (a : Fin 3) := physicalMixedProfileCoefficient g1 L lam δ R p h a
  let conn (a b c : Fin 3) := physicalMixedConnectionCoefficient g1 L lam h a b c
  let pure (a b : Fin 3) := physicalPureAngularCoefficient g1 L lam δ R p h a b
  have hprofS (a : Fin 3) : ContDiff ℝ ∞ (prof a) :=
    contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhe a
  have hconnS (a b c : Fin 3) : ContDiff ℝ ∞ (conn a b c) :=
    contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhe a b c
  have hpureS (a b : Fin 3) : ContDiff ℝ ∞ (pure a b) :=
    contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhe a b
  have hMixedj (a b c : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ 2) :=
    hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a b c v hv
  have hprofj (a : Fin 3) : HasCoordinateWordJetBound 2 (prof a) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs, prof, h, Nat.zero_add] using (hMixedj a 0 0 v hv).2.1
  have hconnj (a b c : Fin 3) : HasCoordinateWordJetBound 2 (conn a b c) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs, conn, h, Nat.zero_add] using (hMixedj a b c v hv).2.2.1
  have hpurej (a b : Fin 3) : HasCoordinateWordJetBound 2 (pure a b) x (Cm*eps) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs, pure, h, Nat.zero_add] using (hMixedj a b 0 v hv).2.2.2
  have hScalarFixed (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (S : SphereL2 →L[ℝ] SphereL2)
      (MS : ℝ) (hMS : 0 ≤ MS) (hS : ‖S‖ ≤ MS)
      (hfjet : HasCoordinateWordJetBound 2 f x (Cm*eps) beta 0) :
      HasCoordinateWordJetBound 2 (fun y => f y • S) x (4*Cm*MS*eps) beta 0 := by
    have hSj := hasCoordinateWordJetBound_const_normed 2 S x MS beta hS hb0
    have ht := hasCoordinateWordJetBound_smul 2 f (fun _ : R3 => S) hf contDiff_const
      x (Cm*eps) MS beta 0 0 (mul_nonneg hCm.le heps) hMS hb0 hfjet hSj
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num, Nat.add_zero] <;> ring
  have hPj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => prof a y • SP a)
      x (4*Cm*MP*eps) beta 0 :=
    hScalarFixed (prof a) (hprofS a) (SP a) MP hMP (hSP a) (hprofj a)
  let FP : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, prof a y • SP a
  have hFPS : ContDiff ℝ ∞ FP := ContDiff.sum (fun a _ => (hprofS a).smul contDiff_const)
  have hPsum : HasCoordinateWordJetBound 2 FP x (12*Cm*MP*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun a y => prof a y • SP a)
      (fun a => (hprofS a).smul contDiff_const) x (4*Cm*MP*eps) beta 0 hPj
    convert ht using 1 <;> simp only [FP, Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hConnj (a b c : Fin 3) : HasCoordinateWordJetBound 2 (fun y => conn a b c y • SC a b c)
      x (4*Cm*MC*eps) beta 0 :=
    hScalarFixed (conn a b c) (hconnS a b c) (SC a b c) MC hMC (hSC a b c) (hconnj a b c)
  let FC : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SC a b c
  have hFCS : ContDiff ℝ ∞ FC := ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const)))
  have hCsum2 (a b : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ c : Fin 3, conn a b c y • SC a b c) x (12*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun c y => conn a b c y • SC a b c)
      (fun c => (hconnS a b c).smul contDiff_const) x (4*Cm*MC*eps) beta 0 (hConnj a b)
    convert ht using 1 <;> simp only [Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hCsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SC a b c) x (36*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun b y => ∑ c : Fin 3, conn a b c y • SC a b c)
      (fun b => ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const))
      x (12*Cm*MC*eps) beta 0 (hCsum2 a)
    convert ht using 1 <;> simp only [Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hCsum : HasCoordinateWordJetBound 2 FC x (108*Cm*MC*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2
      (fun a y => ∑ b : Fin 3, ∑ c : Fin 3, conn a b c y • SC a b c)
      (fun a => ContDiff.sum (fun b _ => ContDiff.sum (fun c _ => (hconnS a b c).smul contDiff_const)))
      x (36*Cm*MC*eps) beta 0 hCsum1
    convert ht using 1 <;> simp only [FC, Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hUj (a b : Fin 3) : HasCoordinateWordJetBound 2 (fun y => pure a b y • SU a b)
      x (4*Cm*MU*eps) beta 0 :=
    hScalarFixed (pure a b) (hpureS a b) (SU a b) MU hMU (hSU a b) (hpurej a b)
  let FU : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, ∑ b : Fin 3, pure a b y • SU a b
  have hFUS : ContDiff ℝ ∞ FU :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const))
  have hUsum1 (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => ∑ b : Fin 3, pure a b y • SU a b) x (12*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun b y => pure a b y • SU a b)
      (fun b => (hpureS a b).smul contDiff_const) x (4*Cm*MU*eps) beta 0 (hUj a)
    convert ht using 1 <;> simp only [Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hUsum : HasCoordinateWordJetBound 2 FU x (36*Cm*MU*eps) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun a y => ∑ b : Fin 3, pure a b y • SU a b)
      (fun a => ContDiff.sum (fun b _ => (hpureS a b).smul contDiff_const))
      x (12*Cm*MU*eps) beta 0 hUsum1
    convert ht using 1 <;> simp only [FU, Fintype.card_fin, Nat.cast_ofNat] <;> ring
  have hKP := hasCoordinateWordJetBound_add 2 K0 FP hK0S hFPS x
    (CK*eps) (12*Cm*MP*eps) beta 0 hK0j hPsum
  have hKPC := hasCoordinateWordJetBound_add 2 (fun y => K0 y+FP y) FC
    (hK0S.add hFPS) hFCS x (CK*eps+12*Cm*MP*eps) (108*Cm*MC*eps) beta 0 hKP hCsum
  have hKPCU := hasCoordinateWordJetBound_add 2 (fun y => K0 y+FP y+FC y) FU
    ((hK0S.add hFPS).add hFCS) hFUS x
    (CK*eps+12*Cm*MP*eps+108*Cm*MC*eps) (36*Cm*MU*eps) beta 0 hKPC hUsum
  have hAll := hasCoordinateWordJetBound_add 2 (fun y => K0 y+FP y+FC y+FU y) J0
    (((hK0S.add hFPS).add hFCS).add hFUS) hJ0S x
    (CK*eps+12*Cm*MP*eps+108*Cm*MC*eps+36*Cm*MU*eps) (CJ*eps) beta 0 hKPCU hJ0j
  have hScale : CK*eps+12*Cm*MP*eps+108*Cm*MC*eps+36*Cm*MU*eps+CJ*eps ≤ C*eps := by
    dsimp only [C]
    nlinarith
  have ht := (hasCoordinateWordJetBound_mono 2 _ x _ (C*eps) beta 0 hAll hScale hb0) w hw
  have hCoefficient : (fun y => K0 y+FP y+FC y+FU y+J0 y) =
      nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p := by
    funext y
    simp only [nativeCSecondAngularCoefficient, K0, FP, FC, FU, J0, prof, conn, pure,
      h, SP, SC, SU, I, Id, ContinuousLinearMap.comp_assoc]
  rw [hCoefficient] at ht
  simpa only [Nat.zero_add] using ht

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
