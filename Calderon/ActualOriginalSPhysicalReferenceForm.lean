import Calderon.ActualOriginalSPhysicalSmallForm
import Calderon.FiniteCoreSobolevDerivativeEnergy
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
/- Root, before-source mathematical expansion in UPFRONT.md; pending parent qualification. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalReferenceForm
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
  ActualHorizontalNormBridge ActualHigherSIntegratedPairing PrincipalCommutator BaseDensityAdjoint
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma matrix_sum_norm_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → E) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ i a, |c i a| ≤ M) :
    (∑ i : Fin 3, ‖∑ a : Fin 3, c i a • v a‖^2) ≤ 9*M^2*(∑ a : Fin 3, ‖v a‖^2) := by
  have hS0 : 0 ≤ ∑ a : Fin 3, ‖v a‖ := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hS2 : (∑ a : Fin 3, ‖v a‖)^2 ≤ 3*(∑ a : Fin 3, ‖v a‖^2) := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),sq_nonneg (‖v 1‖-‖v 2‖)]
  have hrow (i : Fin 3) : ‖∑ a : Fin 3, c i a • v a‖^2 ≤ 3*M^2*(∑ a : Fin 3, ‖v a‖^2) := by
    have hn : ‖∑ a : Fin 3, c i a • v a‖ ≤ M*(∑ a : Fin 3, ‖v a‖) := by
      calc _ ≤ ∑ a : Fin 3, ‖c i a • v a‖ := norm_sum_le _ _
           _ ≤ ∑ a : Fin 3, M*‖v a‖ := Finset.sum_le_sum (fun a _ => by
             simpa only [norm_smul,Real.norm_eq_abs] using
               mul_le_mul_of_nonneg_right (hc i a) (norm_nonneg (v a)))
           _ = _ := by rw [Finset.mul_sum]
    have hn2 := mul_self_le_mul_self (norm_nonneg _) hn
    have hs := mul_le_mul_of_nonneg_left hS2 (sq_nonneg M)
    nlinarith only [hn2,hs]
  calc _ ≤ ∑ _i : Fin 3, 3*M^2*(∑ a : Fin 3, ‖v a‖^2) := Finset.sum_le_sum (fun i _ => hrow i)
       _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma apply_reference_frame {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MatrixField) (L q : ℝ) (x : R3) (i : Fin 3) (T : R3 →L[ℝ] E) :
    T (referenceMetricGramFrame g L (q,x) i) =
      ∑ a : Fin 3, ActualBalancedFirstPrincipalError.frameEntry g L i a (q,x) • T (coordinateDirection a) := by
  rw [referenceGramFrame_eq_sum_coordinateDirection g L q x i,map_sum]
  simp only [map_smul]

private lemma sum_reference_frame_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MatrixField) (L q : ℝ) (x : R3) (T : R3 →L[ℝ] E) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ i a, |ActualBalancedFirstPrincipalError.frameEntry g L i a (q,x)| ≤ M) :
    (∑ i : Fin 3, ‖T (referenceMetricGramFrame g L (q,x) i)‖^2) ≤
      9*M^2*(∑ a : Fin 3, ‖T (coordinateDirection a)‖^2) := by
  calc _ = ∑ i : Fin 3, ‖∑ a : Fin 3,
      ActualBalancedFirstPrincipalError.frameEntry g L i a (q,x) • T (coordinateDirection a)‖^2 :=
       Finset.sum_congr rfl (fun i _ => congrArg (fun v : E => ‖v‖^2) (apply_reference_frame g L q x i T))
       _ ≤ _ := matrix_sum_norm_sq_le _ _ M hM hc

private lemma scale_frame_energy (a b u d h : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hu : 0 ≤ u) (hd : 0 ≤ d) (hh : h ≤ a*d) :
    b⁻¹*h+b*u ≤ (a+1)*(b⁻¹*d+b*u) := by
  have hi : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have h1 := mul_le_mul_of_nonneg_left hh hi
  have h2 : 0 ≤ b⁻¹*d+a*b*u := add_nonneg (mul_nonneg hi hd) (by positivity)
  nlinarith only [h1,h2]

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "UF" => ActualHigherSFormation.higherSInput hO hD

/-- The literal frame derivative energy before multiplication by the physical base density. -/
def frameDerivativeEnergy (g : MatrixField) (L q b : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  b⁻¹*(∑ i : Fin 3, ‖IH (fderiv ℝ (UF F) x (referenceMetricGramFrame g L (q,x) i))‖^2)+
    b*‖UF F x‖^2

attribute [local irreducible] referenceMetricGramFrame ActualBalancedFirstPrincipalError.frameEntry
  sphereSobolevInclusionL

/-- Uniform comparison with the existing reference four-term energy, using genuine frame derivatives. -/
theorem exists_frameDerivativeEnergy_uniform_reference_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ b : ℝ, 1 ≤ b →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      frameDerivativeEnergy hO hD g L q b F x ≤
        C*finiteCoreReferenceProfileEnergy hO hD g hg L q b F x := by
  obtain ⟨M,hM,hGeom⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  obtain ⟨Cr,hCr,hRef⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD g hg L K hK
  refine ⟨(9*M^2+1)*Cr,mul_pos (by positivity) hCr,?_⟩
  intro q hq x hx b hb F
  let u : R3 → Hi := UF F
  let T : R3 →L[ℝ] Half := ContinuousLinearMap.comp IH (fderiv ℝ u x)
  have hQ : (∑ i : Fin 3, ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖^2) ≤
      9*M^2*(∑ a : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection a))‖^2) :=
    sum_reference_frame_sq_le g L q x T M (zero_le_one.trans hM) (hGeom q hq x hx).1
  have hSource : b⁻¹*(∑ a : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection a))‖^2)+b*‖u x‖^2 ≤
      finiteCoreSourceEnergy hO hD b F x :=
    native_threeHalf_angular_energy_le_finiteCoreSourceEnergy hO hD b F x
  have hFrame := scale_frame_energy (9*M^2) b (‖u x‖^2)
    (∑ a : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection a))‖^2)
    (∑ i : Fin 3, ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖^2)
    (by positivity) (lt_of_lt_of_le zero_lt_one hb) (sq_nonneg _)
    (Finset.sum_nonneg (fun a _ => sq_nonneg _)) hQ
  calc frameDerivativeEnergy hO hD g L q b F x ≤
          (9*M^2+1)*(b⁻¹*(∑ a : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection a))‖^2)+b*‖u x‖^2) := hFrame
       _ ≤ (9*M^2+1)*finiteCoreSourceEnergy hO hD b F x := mul_le_mul_of_nonneg_left hSource (by positivity)
       _ ≤ (9*M^2+1)*(Cr*finiteCoreReferenceProfileEnergy hO hD g hg L q b F x) :=
         mul_le_mul_of_nonneg_left (hRef q hq x hx b hb F) (by positivity)
       _ = _ := by ring

private lemma physicalDerivativeEnergy_eq_zero_of_notMem (g : MatrixField) (L δr Ar : ℝ)
    (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ tsupport F.val) :
    ActualOriginalSPhysicalSmallForm.physicalDerivativeEnergy g L hO hD δr Ar p q F x = 0 := by
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hxU : x ∉ tsupport (UF F) := fun h => hx (hRep.2.2.1 h)
  have hu : UF F x = 0 := image_eq_zero_of_notMem_tsupport hxU
  have hd : fderiv ℝ (UF F) x = 0 := fderiv_of_notMem_tsupport ℝ hxU
  unfold ActualOriginalSPhysicalSmallForm.physicalDerivativeEnergy
  simp only [hu,hd,ContinuousLinearMap.zero_apply,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,mul_zero,add_zero]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "TS" F:max => tsupport (F : R3 → SphereL2)
local notation "BETA" => ReferenceWeightedApproximation.actualReferenceBeta g L
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EN" => ActualOriginalSPhysicalSmallForm.physicalDerivativeEnergy g L hO hD

/-- Original full S small form in the existing reference profile energy; no new regularity premise. -/
theorem exists_retained_original_S_small_reference_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q : ℝ,
        ∀ F : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x ∈ TS F, 1 ≤ BETA q δr Ar p x) →
          (∀ x ∈ TS F, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ η) →
          Integrable (fun x => referenceDensityFamily g L (q,x)*
            ⟪F.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 F x⟫_ℝ) ∧
          Integrable (fun x => referenceDensityFamily g L (q,x)*
            finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) ∧
          |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 F x⟫_ℝ| ≤
            K*η*∫ x, referenceDensityFamily g L (q,x)*
              finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x := by
  obtain ⟨Cg,hCg,hPoint⟩ := exists_frameDerivativeEnergy_uniform_reference_bound hO hD g hg L
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨δ,hδ,Cm,hMetrics⟩ := ActualOriginalSPhysicalSmallForm.exists_retained_original_S_small_physical_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W hL
  refine ⟨δ,hδ,Cm,?_⟩
  intro g2 hg2
  obtain ⟨Ks,hKs,hS⟩ := hMetrics g2 hg2
  refine ⟨Ks*Cg,mul_pos hKs hCg,?_⟩
  intro η hη hη1 δr Ar p hδr hδr1 hAr hp q F hTF hβ1 hRβ
  obtain ⟨hSi,hEi,hSb⟩ := hS η hη hη1 δr Ar p hδr hδr1 hAr hp q F hTF hβ1 hRβ
  have hβc := ReferenceWeightedApproximation.continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hβpos := ReferenceWeightedApproximation.actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hNi := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p) hβc hβpos F
  have hPt : ∀ x, EN δr Ar p q F x ≤ Cg*(referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) := by
    intro x
    by_cases hx : x ∈ TS F
    · have ht := hTF x hx
      have hp := hPoint q ht.1.1 x ht.1.2.1 (BETA q δr Ar p x) (hβ1 x hx) F
      calc EN δr Ar p q F x = referenceDensityFamily g L (q,x)*
          frameDerivativeEnergy hO hD g L q (BETA q δr Ar p x) F x := rfl
           _ ≤ referenceDensityFamily g L (q,x)*(Cg*
             finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) :=
             mul_le_mul_of_nonneg_left hp (referenceDensityFamily_pos g hg L (q,x)).le
           _ = _ := by ring
    · rw [physicalDerivativeEnergy_eq_zero_of_notMem hO hD g L δr Ar p q F x hx]
      exact mul_nonneg hCg.le (mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (BETA q δr Ar p x) (hβpos x).le F x))
  have hInt := integral_mono hEi (hNi.const_mul Cg) hPt
  rw [integral_const_mul] at hInt
  refine ⟨hSi,hNi,?_⟩
  calc _ ≤ Ks*η*(∫ x, EN δr Ar p q F x) := hSb
       _ ≤ Ks*η*(Cg*∫ x, referenceDensityFamily g L (q,x)*
         finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) :=
         mul_le_mul_of_nonneg_left hInt (mul_nonneg hKs.le hη.le)
       _ = _ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalReferenceForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalReferenceForm.exists_frameDerivativeEnergy_uniform_reference_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSPhysicalReferenceForm.exists_retained_original_S_small_reference_form
