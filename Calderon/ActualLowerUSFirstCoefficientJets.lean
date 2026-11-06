import Calderon.ActualLowerUSSecondRowCoefficients
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets

/-!
GPT-6.1 Sol authoring support. Before-code expansion:
lower-u-s-nov03-v001/second-row-next-upfront.md.
Original raw angular coefficient jets only; no physical endpoint cap premise.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicModel ActualPhysicalMixedFirst
  ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  AmbientReferenceCovariantCore ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  CoordinateBootstrapJets NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation ConformalDepth PrincipalCommutator ReferenceDensityBounds

variable (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

include hg hg2

include hdr hAr in
theorem contDiff_firstAngularCoefficient (i : Fin 3) (v : FirstAngularIndex) :
    ContDiff ℝ ∞ (fun x => firstAngularCoefficient g L g2 q dr Ar p i x v) := by
  cases v with
  | inl V =>
    cases V with
    | inr z => exact (contDiff_nativeFirstDegreeCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i).neg
    | inl bd =>
      apply contDiff_const.mul
      apply ContDiff.sum
      intro c _hc
      exact (contDiff_nativeFirstConnectionCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i c).mul
        (contDiff_referenceFrameConnectionCoefficient_field g hg L q _
          (contDiff_referenceMetricGramFrame_slice g hg L q c) bd.1 bd.2)
  | inr b =>
    exact (contDiff_physicalMixedFirstCoefficient g hg L q _
      (fun j k => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q j k) b i).neg

/-- Fixed-g2 raw coefficient words, through one original coordinate derivative.
Every coefficient is assembled from original H8/profile/reference data. -/
theorem exists_firstAngularCoefficient_uniform_word_bound
    (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i : Fin 3, ∀ v : FirstAngularIndex,
      HasCoordinateWordJetBound 1 (fun y => firstAngularCoefficient g L g2 q dr Ar p i y v) x
        (CJ*referenceRadius dr Ar p L x) (actualReferenceBeta g L q dr Ar p x) 1 := by
  obtain ⟨J,hJ,hJets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds
    g g2 hg hg2 L hL K hK
  let CJ : ℝ := 1+J+6*J^2
  have hCJ : 0 < CJ := by dsimp only [CJ]; positivity
  have hJCJ : J ≤ CJ := by dsimp only [CJ]; nlinarith [sq_nonneg J]
  have hJ2CJ : 6*J^2 ≤ CJ := by dsimp only [CJ]; linarith
  refine ⟨CJ,hCJ,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i v
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb0 : 0 ≤ beta := (show (0:ℝ) ≤ 1 by norm_num).trans hb
  have hjets := hJets q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs
  have hd : HasCoordinateWordJetBound 1 (nativeFirstDegreeCoefficient g g2 L q dr Ar p i)
      x (J*r) beta 1 := by
    intro word hw
    simpa only [Real.norm_eq_abs,mul_assoc] using
      (hjets word (hw.trans (by norm_num)) i 0 0 0).2.2.1
  have hk (c : Fin 3) : HasCoordinateWordJetBound 1
      (nativeFirstConnectionCoefficient g g2 L q dr Ar p i c) x (J*r) beta 0 := by
    intro word hw
    simpa only [Real.norm_eq_abs,Nat.zero_add,mul_assoc] using
      (hjets word (hw.trans (by norm_num)) i 0 0 c).2.2.2.1
  have hΓ (c b d : Fin 3) : HasCoordinateWordJetBound 1
      (fun y => referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) c) b d) x J beta 0 := by
    intro word hw
    simpa only [Real.norm_eq_abs,Nat.zero_add] using
      (hjets word (hw.trans (by norm_num)) i d b c).2.2.2.2.1
  have hm (b : Fin 3) : HasCoordinateWordJetBound 1
      (physicalMixedFirstCoefficient g L q (referenceNormalizedPrincipalDifference g g2 L q) b i)
      x (J*r) beta 0 := by
    intro word hw
    have hh := (hjets word (hw.trans (by norm_num)) i b 0 0).1
    have he : J*eta*r*beta^word.length ≤ (J*r)*beta^word.length :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hJ.le hr.le]) (pow_nonneg hb0 _)
    simpa only [Nat.zero_add] using
      (by simpa only [Real.norm_eq_abs,Nat.zero_add] using hh :
        ‖coordinateFieldWordPartial word _ x‖ ≤ J*eta*r*beta^word.length).trans he
  cases v with
  | inl V =>
    cases V with
    | inr z =>
      exact hasCoordinateWordJetBound_mono 1 _ x (J*r) (CJ*r) beta 1
        (hasCoordinateWordJetBound_neg 1 _
          (contDiff_nativeFirstDegreeCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i)
          x (J*r) beta 1 hd) (mul_le_mul_of_nonneg_right hJCJ hr.le) hb0
    | inl bd =>
      let f : Fin 3 → R3 → ℝ := fun c y => nativeFirstConnectionCoefficient g g2 L q dr Ar p i c y *
        referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) c) bd.1 bd.2
      have hf (c : Fin 3) : ContDiff ℝ ∞ (f c) :=
        (contDiff_nativeFirstConnectionCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i c).mul
          (contDiff_referenceFrameConnectionCoefficient_field g hg L q _
            (contDiff_referenceMetricGramFrame_slice g hg L q c) bd.1 bd.2)
      have hprod (c : Fin 3) : HasCoordinateWordJetBound 1 (f c) x (2*J^2*r) beta 0 := by
        have hh := hasCoordinateWordJetBound_mul 1 _ _
          (contDiff_nativeFirstConnectionCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i c)
          (contDiff_referenceFrameConnectionCoefficient_field g hg L q _
            (contDiff_referenceMetricGramFrame_slice g hg L q c) bd.1 bd.2)
          x (J*r) J beta 0 0 (mul_nonneg hJ.le hr.le) hJ.le hb0 (hk c) (hΓ c bd.1 bd.2)
        convert hh using 1 <;> ring
      have hsum : HasCoordinateWordJetBound 1 (fun y => ∑ c : Fin 3, f c y)
          x (6*J^2*r) beta 0 := by
        have hh := hasCoordinateWordJetBound_sum 1 f hf x (2*J^2*r) beta 0 hprod
        have he : (3:ℝ)*(2*J^2*r) = 6*J^2*r := by ring
        simpa only [Fintype.card_fin,Nat.cast_ofNat,he] using hh
      have hc : HasCoordinateWordJetBound 1 (fun _ : R3 => -(1/2 : ℝ)) x (1/2) beta 0 :=
        hasCoordinateWordJetBound_const 1 _ x _ beta (by norm_num) hb
      have htotal := hasCoordinateWordJetBound_mul 1 (fun _ : R3 => -(1/2 : ℝ))
        (fun y => ∑ c : Fin 3, f c y) contDiff_const (ContDiff.sum fun c _ => hf c)
        x (1/2) (6*J^2*r) beta 0 0 (by norm_num) (by positivity) hb0 hc hsum
      have ht : HasCoordinateWordJetBound 1 (fun y => firstAngularCoefficient g L g2 q dr Ar p i y (Sum.inl (Sum.inl bd)))
          x (6*J^2*r) beta 0 := by
        convert htotal using 1 <;> first | rfl | ring
      exact hasCoordinateWordJetBound_mono 1 _ x (6*J^2*r) (CJ*r) beta 1
        (hasCoordinateWordJetBound_raise_degree 1 _ x (6*J^2*r) beta 0 1
          (by positivity) hb (by norm_num) ht)
        (mul_le_mul_of_nonneg_right hJ2CJ hr.le) hb0
  | inr b =>
    have hm1 := hasCoordinateWordJetBound_raise_degree 1 _ x (J*r) beta 0 1
      (mul_nonneg hJ.le hr.le) hb (by norm_num) (hm b)
    exact hasCoordinateWordJetBound_mono 1 _ x (J*r) (CJ*r) beta 1
      (hasCoordinateWordJetBound_neg 1 _
        (contDiff_physicalMixedFirstCoefficient g hg L q _
          (fun j k => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q j k) b i)
        x (J*r) beta 1 hm1) (mul_le_mul_of_nonneg_right hJCJ hr.le) hb0

/-- Original-profile pointwise coefficient and coordinate first-derivative
rates, with the constant chosen before q and all radius/profile parameters. -/
theorem exists_firstAngularCoefficient_uniform_first_bounds
    (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i : Fin 3, ∀ v : FirstAngularIndex,
      |firstAngularCoefficient g L g2 q dr Ar p i x v| ≤ CJ*eta/actualReferenceBeta g L q dr Ar p x ∧
      ∀ k : Fin 3, |directionalFDeriv (coordinateDirection k)
        (fun y => firstAngularCoefficient g L g2 q dr Ar p i y v) x| ≤ CJ*eta := by
  obtain ⟨CJ,hCJ,hWord⟩ := exists_firstAngularCoefficient_uniform_word_bound g g2 hg hg2 L hL K hK
  refine ⟨CJ,hCJ,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i v
  have hw := hWord q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i v
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hbpos : 0 < beta := by change 1 ≤ beta at hb; linarith
  have hrb : r*beta ≤ eta/beta := (le_div_iff₀ hbpos).2 (by change r*beta^2 ≤ eta at hs; nlinarith)
  have h0 := hw [] (by simp)
  have h0' : |firstAngularCoefficient g L g2 q dr Ar p i x v| ≤ CJ*r*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,Real.norm_eq_abs] using h0
  refine ⟨h0'.trans ?_,?_⟩
  · calc
      CJ*r*beta = CJ*(r*beta) := by ring
      _ ≤ CJ*(eta/beta) := mul_le_mul_of_nonneg_left hrb hCJ.le
      _ = CJ*eta/beta := by ring
  · intro k
    have h1 := hw [k] (by simp)
    have h1' : |directionalFDeriv (coordinateDirection k)
        (fun y => firstAngularCoefficient g L g2 q dr Ar p i y v) x| ≤ CJ*r*beta^2 := by
      simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,
        Nat.zero_add,Nat.add_zero,Real.norm_eq_abs] using h1
    exact h1'.trans (by change r*beta^2 ≤ eta at hs; nlinarith)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
