import Calderon.ActualFiniteHarmonicModelFirstAngularBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore BoundedAngularShift
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients ActualNormalizedSecondModelErrorAssembly
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
theorem exists_modelFirstNormalizedCoefficient_uniform_coordinate_word_smallness (hF : SphereFischerInner) (g1 g2 : MatrixField)
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
        (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x‖ ≤
          (C * eps / beta) * beta^w.length := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 3
  obtain ⟨CK,hCK,hDD⟩ := exists_referenceDD_normalized_trace_uniform_coordinate_word_smallness
    hO hD g1 hg1 L hL K hK 2 (by norm_num)
  obtain ⟨CJ,hCJ,hDrift⟩ := exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 2
  let S (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 := normalizedRaising hF hO hD a
  let MS : ℝ := 1 + ∑ a : Fin 3, ‖S a‖
  let Dm : ℝ := 6*(2 : ℝ)^3*M
  let CB : ℝ := 1 + CK + 12*Dm*MS + CJ
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMS : 1 ≤ MS := by
    dsimp only [MS]
    have hh : 0 ≤ ∑ a : Fin 3, ‖S a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hMS0 : 0 ≤ MS := le_trans zero_le_one hMS
  have hDm : 0 ≤ Dm := by dsimp only [Dm]; positivity
  have hCB : 0 < CB := by dsimp only [CB]; positivity
  have hS (a : Fin 3) : ‖S a‖ ≤ MS := by
    have hh : ‖S a‖ ≤ ∑ b : Fin 3, ‖S b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg (S b)) (Finset.mem_univ a)
    dsimp only [MS]
    linarith
  refine ⟨CB,hCB,?_⟩
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
  let B : R3 → SphereL2 →L[ℝ] SphereL2 :=
    referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  let m (a : Fin 3) : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam h a j
  let J : R3 → SphereL2 →L[ℝ] SphereL2 :=
    normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j
  have hBS : ContDiff ℝ ∞ B :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hmS (a : Fin 3) : ContDiff ℝ ∞ (m a) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hJS : ContDiff ℝ ∞ J :=
    contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR j
  have hBj : HasCoordinateWordJetBound 2 B x (CK*Rate) beta 0 := by
    intro v hv
    have ht := (hDD lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh x hx
      hb hH8 hsmall v hv).1 j
    simpa only [B,Rate,beta,actualReferenceBeta,Nat.zero_add,mul_div_assoc] using ht
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
  have hMixS : ContDiff ℝ ∞ (fun y => ∑ a : Fin 3, m a y • S a) :=
    ContDiff.sum (fun a _ => (hmS a).smul contDiff_const)
  have h0 := hasCoordinateWordJetBound_add 2 B (fun y => ∑ a : Fin 3, m a y • S a)
    hBS hMixS x (CK*Rate) (12*Dm*MS*Rate) beta 0 hBj hMixSum'
  have h1 := hasCoordinateWordJetBound_add 2 (fun y => B y+∑ a : Fin 3, m a y • S a) J
    (hBS.add hMixS) hJS x (CK*Rate+12*Dm*MS*Rate) (CJ*Rate) beta 0 h0 hJj
  change HasCoordinateWordJetBound 2
    (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x
    ((CK*Rate+12*Dm*MS*Rate)+CJ*Rate) beta 0 at h1
  have hsum : (CK*Rate+12*Dm*MS*Rate)+CJ*Rate = (CB-1)*Rate := by
    dsimp only [CB]
    ring
  have hscale : (CK*Rate+12*Dm*MS*Rate)+CJ*Rate ≤ CB*eps/beta := by
    rw [hsum]
    calc
      (CB-1)*Rate ≤ CB*Rate := mul_le_mul_of_nonneg_right (by linarith) hRate
      _ = CB*eps/beta := by dsimp only [Rate]; ring
  exact (h1 w hw).trans (by simpa only [Nat.zero_add] using
    mul_le_mul_of_nonneg_right hscale (pow_nonneg hb0 w.length))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
