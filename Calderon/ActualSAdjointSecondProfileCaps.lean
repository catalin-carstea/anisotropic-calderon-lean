import Calderon.ActualSAdjointSecondPointwiseBound
import Calderon.ActualReverseEOrdinaryCaps
import Calderon.ActualSecondGeometryCaps
import Calderon.ActualSecondDensityProfileCaps
import Calderon.ActualSScalarCoefficientBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondProfileCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualHigherSSecondAdjoint ActualSAdjointSecondNegative ActualSAdjointSecondPointwiseBound
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift ActualHorizontalNormBridge
  ActualSecondGeometryCaps ActualSecondDensityProfileCaps ActualSScalarCoefficientBounds
  ActualReverseEOrdinaryCaps ActualCommonFirstWordQuadraticAdjoint ActualBalancedFirstPrincipalError

private lemma map_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (u : E) (M D : ℝ) (hA : ‖A‖ ≤ M) (hu : ‖u‖ ≤ D) (hM : 0 ≤ M) :
    ‖A u‖ ≤ M*D :=
  (A.le_opNorm u).trans (mul_le_mul hA hu (norm_nonneg u) hM)

private lemma smul_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (v : E) (A D : ℝ) (hc : |c| ≤ A) (hv : ‖v‖ ≤ D) (hA : 0 ≤ A) :
    ‖c • v‖ ≤ A*D := by
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hc hv (norm_nonneg v) hA

private lemma norm_three_of_caps {E : Type*} [NormedAddCommGroup E]
    (a b c : E) (A B C : ℝ) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a+b+c‖ ≤ A+B+C := by
  have h1 := norm_add_le (a+b) c
  have h2 := norm_add_le a b
  linarith

private lemma included_frame_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (I : E →L[ℝ] F) (D : R3 →L[ℝ] E)
    (g : MatrixField) (L q : ℝ) (x : R3) (i : Fin 3) (A : ℝ)
    (hA : ∀ k : Fin 3, |referenceMetricGramFrame g L (q,x) i k| ≤ A) :
    ‖I (D (referenceMetricGramFrame g L (q,x) i))‖ ≤
      A*∑ k : Fin 3, ‖I (D (coordinateDirection k))‖ := by
  calc
    _ = ‖∑ k : Fin 3, frameEntry g L i k (q,x) • I (D (coordinateDirection k))‖ := by
      rw [referenceGramFrame_eq_sum_coordinateDirection g L q x i]
      simp only [map_sum,map_smul]
    _ ≤ ∑ k : Fin 3, ‖frameEntry g L i k (q,x) • I (D (coordinateDirection k))‖ :=
      norm_sum_le _ _
    _ = ∑ k : Fin 3, |frameEntry g L i k (q,x)| *‖I (D (coordinateDirection k))‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ k : Fin 3, A*‖I (D (coordinateDirection k))‖ :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Uin" => higherSInput hO hD
local notation "PC" => SecondPointwiseCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] reverseEHigh reverseELow sphereSobolevInclusionL
  sphereSobolevShiftedDegreeL referenceHighWeightedHorizontalAction referenceLowerHorizontalAngularL
  referenceHighHorizontalAngularL

/-- Every raw cap is produced; eta0 precedes g2 and M precedes every profile/input. -/
theorem exists_secondPointwiseCaps (hL : 0 < L) (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ F : smoothCompactFiniteSphereCore hO hD, PC g2 dr Ar p q F x M := by
  classical
  let data := Classical.choice (exists_reverseEOrdinaryPhysicalCaps g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hL hreg δ0 W δ Cm)
  refine ⟨data.eta0,data.eta0_pos,data.eta0_le,?_⟩
  intro g2 hg2
  obtain ⟨A,hA,hGeom⟩ := exists_geometryCaps g g2 hg hg2 L
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cf,hCf,hLog⟩ := exists_profile_horizontal_log_derivative_bound g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cd,hCd,hDen⟩ := exists_second_density_uniform_profile_bound g g2 hg hg2 L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let NI : ℝ := ‖IH‖
  let NJ : ℝ := ‖JL‖
  let NBH : ℝ := ‖sphereSobolevShiftedDegreeL (3/2 : ℝ)‖
  let NBL : ℝ := ‖sphereSobolevShiftedDegreeL (1/2 : ℝ)‖
  let Dir : ℝ := data.M*data.KT*A
  let Cref : ℝ := 2*A+Cf*NBH
  let BM : ℝ := 1+A+data.M+Dir+NI+NJ+NBH+NBL+Cf+Cd+Cref
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hE0 := data.M_nonneg
  have hD0 : 0 ≤ Dir := mul_nonneg (mul_nonneg data.M_nonneg data.KT_pos.le) hA0
  have hI0 : 0 ≤ NI := norm_nonneg _
  have hJ0 : 0 ≤ NJ := norm_nonneg _
  have hBH0 : 0 ≤ NBH := norm_nonneg _
  have hBL0 : 0 ≤ NBL := norm_nonneg _
  have hR0 : 0 ≤ Cref := by dsimp [Cref]; positivity
  have hAll : 1 ≤ BM ∧ A ≤ BM ∧ data.M ≤ BM ∧ Dir ≤ BM ∧ NI ≤ BM ∧ NJ ≤ BM ∧
      NBH ≤ BM ∧ NBL ≤ BM ∧ Cf ≤ BM ∧ Cd ≤ BM ∧ Cref ≤ BM := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> dsimp only [BM] <;>
      linarith only [hA0,hE0,hD0,hI0,hJ0,hBH0,hBL0,hCf,hCd,hR0]
  rcases hAll with ⟨hB1,hBA,hBE,hBD,hBI,hBJ,hBH,hBL,hBF,hBC,hBR⟩
  refine ⟨BM,hB1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs F
  have gc := hGeom q hq x hx
  have hPH := (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs).2
  let u : Hi := Uin F x
  let m : ℝ := ‖u‖
  let G : ℝ := ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F) x (coordinateDirection k))‖
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let V : ℝ := G+beta*m
  have hm : 0 ≤ m := norm_nonneg u
  have hG : 0 ≤ G := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hV0 : 0 ≤ V := add_nonneg hG (mul_nonneg hb0 hm)
  have hGV : G ≤ V := le_add_of_nonneg_right (mul_nonneg hb0 hm)
  have hbmV : beta*m ≤ V := le_add_of_nonneg_left hG
  have hmV : m ≤ V := by
    have hh : m ≤ beta*m := by nlinarith only [mul_nonneg (sub_nonneg.mpr hb) hm]
    exact hh.trans hbmV
  have hFrame (i : Fin 3) :
      ‖IH (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i))‖ ≤ A*G :=
    included_frame_bound IH (fderiv ℝ (Uin F) x) g L q x i A (gc.frame_entry i)
  have hRef (i : Fin 3) :
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius dr Ar p L) (Uin F) x i‖ ≤ Cref*V := by
    have h1 : ‖IH (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i))‖ ≤ A*V :=
      (hFrame i).trans (mul_le_mul_of_nonneg_left hGV hA0)
    have h2 : ‖referenceHighHorizontalAngularL g L q x i u‖ ≤ A*V :=
      map_bound _ u A V (gc.high_connection i) hmV hA0
    have h3 : ‖referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) u : Half)‖ ≤ (Cf*NBH)*V := by
      calc
        _ ≤ (Cf*beta)*(NBH*m) := smul_bound _ _ _ _
          (hLog dr Ar p hdr hdr1 hAr hp q hq x hx hb i)
          ((sphereSobolevShiftedDegreeL (3/2 : ℝ)).le_opNorm u) (mul_nonneg hCf hb0)
        _ = (Cf*NBH)*(beta*m) := by ring
        _ ≤ (Cf*NBH)*V := mul_le_mul_of_nonneg_left hbmV (mul_nonneg hCf hBH0)
    rw [referenceHighWeightedHorizontalAction,referenceHighHorizontalAction]
    have ht := norm_three_of_caps
      (IH (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i)))
      (referenceHighHorizontalAngularL g L q x i u)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) u : Half))
      (A*V) (A*V) ((Cf*NBH)*V) h1 h2 h3
    exact ht.trans_eq (by dsimp only [Cref]; ring)
  exact {
    one_le := hB1
    density := gc.density.trans hBA
    density_inv := gc.density_inv.trans hBA
    principal := fun i j => (gc.principal i j).trans hBA
    log_radius := fun i => (hLog dr Ar p hdr hdr1 hAr hp q hq x hx hb i).trans
      (mul_le_mul_of_nonneg_right hBF hb0)
    connection := fun i j k => (gc.connection i j k).trans hBA
    drift := fun i => (gc.drift i).trans hBA
    density_derivative := fun i j k => (hDen dr Ar p hdr hdr1 hAr hp q hq x hx hb i j k).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (sq_nonneg _)) hb0)
    high_inclusion := hBI
    low_inclusion := hBJ
    high_degree := hBH
    low_degree := hBL
    low_connection := fun i => (gc.low_connection i).trans hBA
    reverse_high := fun i => (hPH i).1.2.1.trans hBE
    reverse_low := fun i => (hPH i).2.2.1.trans hBE
    reverse_low_directional := fun i j => by
      calc
        _ ≤ ‖fderiv ℝ (fun z => eL i (higherSParam L dr Ar p q z)) x‖*
            ‖referenceMetricGramFrame g L (q,x) j‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (data.M*data.KT)*A := mul_le_mul (hPH i).2.2.2 (gc.frame j)
          (norm_nonneg _) (mul_nonneg data.M_nonneg data.KT_pos.le)
        _ = Dir := rfl
        _ ≤ BM := hBD
    frame_input := fun i => (hFrame i).trans (mul_le_mul_of_nonneg_right hBA hG)
    reference_input := fun i => (hRef i).trans (mul_le_mul_of_nonneg_right hBR hV0)
  }

/-- Full original Second negative cap with no raw analytic-cap assumption, at fixed g2. -/
theorem exists_secondAdjoint_uniform_profile_norm_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ Cs : ℝ, 0 < Cs ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖secondAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖ ≤
        Cs*((referenceRadius dr Ar p L x)^2*
          (∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F) x (coordinateDirection k))‖)+
          (referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x*‖Uin F x‖) := by
  obtain ⟨eta0,he0,he1,hCap⟩ := exists_secondPointwiseCaps g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hL hreg δ0 W δ Cm
  refine ⟨eta0,he0,he1,?_⟩
  intro g2 hg2
  obtain ⟨M,hM,hMC⟩ := hCap g2 hg2
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨200*M^6,by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs F
  exact secondAdjointNegative_bound_of_caps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 dr Ar p q F x M (hMC q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs F) hdr hAr hb

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondProfileCaps
