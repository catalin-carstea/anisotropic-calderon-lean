import Calderon.ActualFiniteHarmonicModelCReversedFormBound
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
private abbrev cReversedCoefficientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] cReversedCoefficientFunction
theorem exists_nativeCReversedFormBound_uniform_smallness
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      nativeCReversedFormBound hO hD g1 g2 hg1 L lam δ R p x ≤ C*eps := by
  classical
  obtain ⟨CK, hCK, hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 2 (by norm_num)
  obtain ⟨Cm, hCm, hMixed⟩ := exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness
    g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CJ, hCJ, hDrift⟩ := exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 2
  let MQ : ℝ := ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖
  let MC : ℝ := 1+∑ b : Fin 3, ∑ c : Fin 3, ‖normalizedRotation hO hD b c‖
  let C : ℝ := 1+CK+CJ+6*Cm*MQ+54*Cm*MC+72*Cm
  have hMQ : 0 ≤ MQ := norm_nonneg _
  have hMC : 0 ≤ MC := by
    have ht : 0 ≤ ∑ b : Fin 3, ∑ c : Fin 3, ‖normalizedRotation hO hD b c‖ :=
      Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => norm_nonneg _))
    dsimp only [MC]
    linarith
  have hC : 0 < C := by
    have hq : 0 ≤ 6*Cm*MQ := mul_nonneg (mul_nonneg (by norm_num) hCm.le) hMQ
    have hr : 0 ≤ 54*Cm*MC := mul_nonneg (mul_nonneg (by norm_num) hCm.le) hMC
    have hm : 0 ≤ 72*Cm := mul_nonneg (by norm_num) hCm.le
    dsimp only [C]
    linarith
  have hRot (b c : Fin 3) : ‖normalizedRotation hO hD b c‖ ≤ MC := by
    have h1 := Finset.single_le_sum (fun k _ => norm_nonneg (normalizedRotation hO hD b k)) (Finset.mem_univ c)
    have h2 : (∑ t : Fin 3, ‖normalizedRotation hO hD b t‖) ≤
        ∑ k : Fin 3, ∑ t : Fin 3, ‖normalizedRotation hO hD k t‖ := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun t _ => norm_nonneg (normalizedRotation hO hD k t))) (Finset.mem_univ b)
    dsimp only [MC]
    linarith
  refine ⟨C, hC, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall
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
  have hk : ‖K0 x‖ ≤ CK*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.zero_add,pow_zero,mul_one] using hK0j [] (by simp)
  have hj : ‖J0 x‖ ≤ CJ*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.zero_add,pow_zero,mul_one] using hJ0j [] (by simp)
  have hp0 (a : Fin 3) : |prof a x| ≤ Cm*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.zero_add,pow_zero,mul_one,Real.norm_eq_abs] using hprofj a [] (by simp)
  have hc0 (a b c : Fin 3) : |conn a b c x| ≤ Cm*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.zero_add,pow_zero,mul_one,Real.norm_eq_abs] using hconnj a b c [] (by simp)
  have hu0 (a b : Fin 3) : |pure a b x| ≤ Cm*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.zero_add,pow_zero,mul_one,Real.norm_eq_abs] using hpurej a b [] (by simp)
  have hp (a : Fin 3) : 2*|prof a x| *MQ ≤ 2*(Cm*eps)*MQ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp0 a) (by norm_num)) hMQ
  have hc (a b c : Fin 3) : 2*|conn a b c x| *‖normalizedRotation hO hD b c‖ ≤
      2*(Cm*eps)*MC := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hc0 a b c) (by norm_num)) (hRot b c)
      (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hCm.le heps))
  have hu (a b : Fin 3) : 8*|pure a b x| ≤ 8*(Cm*eps) :=
    mul_le_mul_of_nonneg_left (hu0 a b) (by norm_num)
  have hps : (∑ a : Fin 3, 2*|prof a x| *MQ) ≤ 6*Cm*MQ*eps := by
    calc
      _ ≤ ∑ a : Fin 3, 2*(Cm*eps)*MQ := Finset.sum_le_sum (fun a _ => hp a)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have hcs : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      2*|conn a b c x| *‖normalizedRotation hO hD b c‖) ≤ 54*Cm*MC*eps := by
    calc
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, 2*(Cm*eps)*MC :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hc a b c)))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have hus : (∑ a : Fin 3, ∑ b : Fin 3, 8*|pure a b x|) ≤ 72*Cm*eps := by
    calc
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, 8*(Cm*eps) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hu a b))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  change ‖K0 x‖ + (∑ a : Fin 3, 2*|prof a x| *MQ) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, 2*|conn a b c x| *‖normalizedRotation hO hD b c‖) +
    (∑ a : Fin 3, ∑ b : Fin 3, 8*|pure a b x|) + ‖J0 x‖ ≤ C*eps
  calc
    _ ≤ CK*eps+6*Cm*MQ*eps+54*Cm*MC*eps+72*Cm*eps+CJ*eps :=
      add_le_add (add_le_add (add_le_add (add_le_add hk hps) hcs) hus) hj
    _ = (C-1)*eps := by dsimp only [C]; ring
    _ ≤ C*eps := mul_le_mul_of_nonneg_right (by linarith) heps

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
