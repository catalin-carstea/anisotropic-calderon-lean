import Calderon.ActualOriginalSDirectPhysicalFormBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalSmallForm
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier SmoothMetricFrame
  MovingFrameConnection ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore
  SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ConformalDepth ActualHorizontalNormBridge ActualHigherSIntegratedPairing
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma weighted_young (u d b : ℝ) (hb : 0 < b) :
    2*u*d ≤ b⁻¹*d^2+b*u^2 := by
  have h := mul_nonneg (inv_nonneg.mpr hb.le) (sq_nonneg (b*u-d))
  have he : b⁻¹*(b*u-d)^2 = b*u^2+b⁻¹*d^2-2*u*d := by
    field_simp
    <;> ring
  rw [he] at h
  linarith

/-- Numerical absorption with a fixed constant, before any native operator substitution. -/
theorem full_majorant_small (r b η u : ℝ) (d : Fin 3 → ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hrb : r*b^2 ≤ η) (hu : 0 ≤ u) (hd : ∀ i, 0 ≤ d i) :
    r^2*u*(∑ i : Fin 3, d i)+(r+r^2*b+r^3)*u^2 ≤
      8*η*(b⁻¹*(∑ i : Fin 3, (d i)^2)+b*u^2) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hb2 : 1 ≤ b^2 := by nlinarith
  have hrη : r ≤ η := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hb2)]
  have hr1 : r ≤ 1 := hrη.trans hη1
  have hr2r : r^2 ≤ r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hr2 : r^2 ≤ η := hr2r.trans hrη
  have hr3 : r^3 ≤ η := by
    have h := mul_le_mul_of_nonneg_right hr2r hr
    nlinarith
  have hr2b : r^2*b ≤ η := by
    calc r^2*b = (r*b)*r := by ring
         _ ≤ (r*b)*b := mul_le_mul_of_nonneg_left (hr1.trans hb) (mul_nonneg hr hb0.le)
         _ = r*b^2 := by ring
         _ ≤ η := hrb
  have hsum : 0 ≤ ∑ i : Fin 3, d i := Finset.sum_nonneg (fun i _ => hd i)
  have hsquares : 0 ≤ ∑ i : Fin 3, (d i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hY : 2*u*(∑ i : Fin 3, d i) ≤ b⁻¹*(∑ i : Fin 3, (d i)^2)+3*b*u^2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => weighted_young u (d i) b hb0)
    simp only [Fin.sum_univ_three] at h ⊢
    nlinarith only [h]
  have hc : r^2*u*(∑ i : Fin 3, d i) ≤
      (η/2)*(b⁻¹*(∑ i : Fin 3, (d i)^2)+3*b*u^2) := by
    have h1 := mul_le_mul_of_nonneg_right hr2 (mul_nonneg hu hsum)
    have h2 := mul_le_mul_of_nonneg_left hY (div_nonneg hη.le (by norm_num : (0:ℝ) ≤ 2))
    nlinarith only [h1,h2]
  have hz : (r+r^2*b+r^3)*u^2 ≤ 3*η*b*u^2 := by
    have h1 := mul_le_mul_of_nonneg_right (add_le_add (add_le_add hrη hr2b) hr3) (sq_nonneg u)
    have h2 := mul_nonneg (mul_nonneg hη.le (sq_nonneg u)) (sub_nonneg.mpr hb)
    nlinarith only [h1,h2]
  have hD := mul_nonneg hη.le (mul_nonneg (inv_nonneg.mpr hb0.le) hsquares)
  have hU := mul_nonneg hη.le (mul_nonneg hb0.le (sq_nonneg u))
  nlinarith only [hc,hz,hD,hU]

private lemma density_full_majorant_small (μ r b η u : ℝ) (d : Fin 3 → ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hb : 1 ≤ b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hrb : r*b^2 ≤ η) (hu : 0 ≤ u) (hd : ∀ i, 0 ≤ d i) :
    μ*(r^2*u*(∑ i : Fin 3, d i)+(r+r^2*b+r^3)*(u*u)) ≤
      (8*η)*(μ*(b⁻¹*(∑ i : Fin 3, (d i)^2)+b*u^2)) := by
  calc _ = μ*(r^2*u*(∑ i : Fin 3, d i)+(r+r^2*b+r^3)*u^2) := by ring
       _ ≤ μ*(8*η*(b⁻¹*(∑ i : Fin 3, (d i)^2)+b*u^2)) :=
         mul_le_mul_of_nonneg_left (full_majorant_small r b η u d hr hb hη hη1 hrb hu hd) hμ
       _ = _ := by ring

private lemma integrable_derivative_energy {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ b : R3 → ℝ) (u : R3 → E) (X : Fin 3 → R3 → R3) (I : E →L[ℝ] H)
    (hμ : Continuous μ) (hb : Continuous b) (hb0 : ∀ x, b x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (hX : ∀ i, Continuous (X i)) :
    Integrable (fun x => μ x * ((b x)⁻¹*(∑ i : Fin 3, ‖I (fderiv ℝ u x (X i x))‖^2)+b x*‖u x‖^2)) := by
  have hi : ∀ i : Fin 3, Continuous (fun x => ‖I (fderiv ℝ u x (X i x))‖^2) := fun i =>
    (((I.continuous.comp ((hu.continuous_fderiv (by simp)).clm_apply (hX i))).norm).pow 2)
  have hc : Continuous (fun x => μ x *
      ((b x)⁻¹*(∑ i : Fin 3, ‖I (fderiv ℝ u x (X i x))‖^2)+b x*‖u x‖^2)) :=
    hμ.mul (((hb.inv₀ hb0).mul (continuous_finset_sum _ (fun i _ => hi i))).add
      (hb.mul (hu.continuous.norm.pow 2)))
  apply ActualHigherSIntegratedPairing.integrable_of_vanish _ hc (tsupport u) huc
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "BETA" => ReferenceWeightedApproximation.actualReferenceBeta g L
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FM" => ActualOriginalSDirectPhysicalFormBounds.fullMajorant g L hO hD

/-- Explicit physical derivative energy. No identification with the manuscript norm N. -/
def physicalDerivativeEnergy (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  referenceDensityFamily g L (q,x) *
    ((BETA q δr Ar p x)⁻¹*(∑ i : Fin 3,
      ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖^2)+
      BETA q δr Ar p x*‖Uin F0 x‖^2)
local notation "EN" => physicalDerivativeEnergy g L hO hD

/-- Complete literal S small form, constant before eta/profiles/inputs/angular degree. -/
theorem exists_retained_original_S_small_physical_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0)
    (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 < K ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q : ℝ,
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
          (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ η) →
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            ⟪F0.val x, SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ) ∧
          Integrable (EN δr Ar p q F0) ∧
          |∫ x, referenceDensityFamily g L (q,x) *
            ⟪F0.val x, SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ| ≤
              K*η*∫ x, EN δr Ar p q F0 x := by
  obtain ⟨δ,hδ,Cm,hMetrics⟩ := ActualOriginalSDirectPhysicalFormBounds.exists_retained_original_fullS_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W hL
  refine ⟨δ,hδ,Cm,?_⟩
  intro g2 hg2
  obtain ⟨K,hK,hBound⟩ := hMetrics g2 hg2
  refine ⟨8*(K+1),by linarith,?_⟩
  intro η hη hη1 δr Ar p hδr hδr1 hAr hp q F0 hTF hβ1 hRβ
  have hβc := ReferenceWeightedApproximation.continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hβpos := ReferenceWeightedApproximation.actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  obtain ⟨hSi,hFMi,hSb⟩ := hBound δr Ar p hδr hδr1 hAr hp q F0 hTF hβ1 hβc
  have hU0 : ∀ z ∉ TS F0, Uin F0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hUc := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUcomp : HasCompactSupport (Uin F0) :=
    ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _ hU0
  have hEi : Integrable (EN δr Ar p q F0) :=
    integrable_derivative_energy (fun x => referenceDensityFamily g L (q,x)) (BETA q δr Ar p)
      (Uin F0) (fun i x => referenceMetricGramFrame g L (q,x) i) IH
      (continuous_density_slice g L q hg) hβc (fun x => (hβpos x).ne') hUc hUcomp
      (fun i => (contDiff_referenceMetricGramFrame_slice g hg L q i).continuous)
  have hEnn : ∀ x, 0 ≤ EN δr Ar p q F0 x := fun x => by
    unfold physicalDerivativeEnergy
    have := (referenceDensityFamily_pos g hg L (q,x)).le
    have := (hβpos x).le
    have := inv_nonneg.mpr (hβpos x).le
    positivity
  have hPt : ∀ x, FM δr Ar p q F0 x ≤ (8*η)*EN δr Ar p q F0 x := by
    intro x
    by_cases hx : x ∈ TS F0
    · exact density_full_majorant_small (referenceDensityFamily g L (q,x))
        (referenceRadius δr Ar p L x) (BETA q δr Ar p x) η ‖Uin F0 x‖
        (fun i => ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖)
        (referenceDensityFamily_pos g hg L (q,x)).le
        (referenceRadius_pos δr Ar p L x hδr hAr).le (hβ1 x hx) hη hη1 (hRβ x hx)
        (norm_nonneg _) (fun i => norm_nonneg _)
    · have hz : FM δr Ar p q F0 x = 0 := by
        unfold ActualOriginalSDirectPhysicalFormBounds.fullMajorant
        simp [hU0 x hx]
      rw [hz]
      exact mul_nonneg (by positivity) (hEnn x)
  have hInt := integral_mono hFMi (hEi.const_mul (8*η)) hPt
  rw [integral_const_mul] at hInt
  have hInt0 : 0 ≤ ∫ x, EN δr Ar p q F0 x := integral_nonneg hEnn
  refine ⟨hSi,hEi,?_⟩
  calc _ ≤ K*(∫ x, FM δr Ar p q F0 x) := hSb
       _ ≤ K*((8*η)*(∫ x, EN δr Ar p q F0 x)) := mul_le_mul_of_nonneg_left hInt hK
       _ ≤ (8*(K+1))*η*(∫ x, EN δr Ar p q F0 x) := by
         nlinarith only [mul_nonneg hη.le hInt0]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalSmallForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalSmallForm.exists_retained_original_S_small_physical_form
