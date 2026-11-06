import Calderon.ActualHigherSAdjointCoefficientBounds
import Calderon.ActualHigherSZeroCoefficientBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSumNegativeBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma norm_first_zero_apply_le {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : Fin 3 → E →L[ℝ] V) (C : F →L[ℝ] V) (d : Fin 3 → E) (u : F)
    (r CB CZ : ℝ) (hB : ∀ i, ‖B i‖ ≤ CB*r^2) (hC : ‖C‖ ≤ CZ*r) :
    ‖(∑ i : Fin 3, B i (d i))+C u‖ ≤ CB*r^2*(∑ i : Fin 3, ‖d i‖)+CZ*r*‖u‖ := by
  have hs : ‖∑ i : Fin 3, B i (d i)‖ ≤ CB*r^2*(∑ i : Fin 3, ‖d i‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖B i (d i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, CB*r^2*‖d i‖ := Finset.sum_le_sum (fun i _ =>
        (ContinuousLinearMap.le_opNorm (B i) (d i)).trans
          (mul_le_mul_of_nonneg_right (hB i) (norm_nonneg (d i))))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hz : ‖C u‖ ≤ CZ*r*‖u‖ := (ContinuousLinearMap.le_opNorm C u).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg u))
  exact (norm_add_le _ _).trans (add_le_add hs hz)

private lemma add_two_weighted_bounds (a b c d K P Z : ℝ)
    (hP : 0 ≤ P) (hZ : 0 ≤ Z) (h1 : a+c ≤ K) (h2 : b+d ≤ K) :
    (a*P+b*Z)+(c*P+d*Z) ≤ K*(P+Z) := by nlinarith

private lemma inner_sub_add_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : ⟪a-b,a+b⟫_ℝ = ‖a‖^2-‖b‖^2 := by
  simp only [inner_sub_left,inner_add_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm b a]
  ring

/-- Universal physical polarization on arbitrary Half outputs, with no finite-output assumption. -/
theorem physical_norm_difference (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : Half) :
    ‖sphereSobolevHalfToSphereL2L hO hD s‖^2 - ‖sphereSobolevHalfToSphereL2L hO hD t‖^2 =
      sphereSobolevDualPairing (1/2 : ℝ) (s-t) (JL (s+t)) := by
  have hp := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD (s-t) (s+t)
  calc
    _ = ⟪sphereSobolevHalfToSphereL2L hO hD s-sphereSobolevHalfToSphereL2L hO hD t,
        sphereSobolevHalfToSphereL2L hO hD s+sphereSobolevHalfToSphereL2L hO hD t⟫_ℝ :=
      (inner_sub_add_norm_sq _ _).symm
    _ = _ := by simpa only [map_sub,map_add] using hp.symm

/-- The signed physical difference consumes a genuine Half difference and a
negative sum graph. This never inverts the Half-to-Neg inclusion. -/
theorem physical_norm_difference_of_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s t d : Half) (n : Neg)
    (hDiff : s-t=d) (hSum : JL (s+t)=n) :
    ‖sphereSobolevHalfToSphereL2L hO hD s‖^2 - ‖sphereSobolevHalfToSphereL2L hO hD t‖^2 =
      sphereSobolevDualPairing (1/2 : ℝ) d n := by
  exact (physical_norm_difference hO hD s t).trans
    (congrArg₂ (fun (u : Half) (v : Neg) => sphereSobolevDualPairing (1/2 : ℝ) u v) hDiff hSum)

section Actual
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
local notation "NEG" => ActualHigherSFormation.nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "ADJ" => ActualHigherSAdjointFormation.higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BF" => ActualHigherSCoefficientExtraction.higherSFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BA" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CA" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] sphereSobolevInclusionL ActualHigherSFormation.higherSInput
  ActualHigherSFormation.nativeHigherSNegative ActualHigherSAdjointFormation.higherSAdjointHalf
  ActualHigherSCoefficientExtraction.higherSFirstFrameCoefficient
  ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointFirstFrameCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient

/-- Original nonnegative first/zero base expression, without angular truncation. -/
def firstZeroBaseEnergy (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (referenceRadius δr Ar p L x)^2 * (∑ i : Fin 3,
    ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖) +
    referenceRadius δr Ar p L x * ‖Uin F0 x‖
local notation "E1" => firstZeroBaseEnergy g L hO hD

lemma firstZeroBaseEnergy_nonneg (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    0 ≤ E1 δr Ar p q F0 x :=
  add_nonneg (mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun i _ => norm_nonneg
      (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))))))
    (mul_nonneg (le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)) (norm_nonneg (Uin F0 x)))

/-- Actual quantitative forward/adjoint NEGATIVE sum bound, uniform before all
profiles and finite inputs. It is not a bound obtained by inverting J. -/
theorem exists_actual_higherS_sum_negative_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
      ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, 1 ≤ actualReferenceBeta g L q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1) →
      ∀ x : R3, ‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x +
        JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ ≤ K*E1 δr Ar p q F0 x := by
  have hFirstFull := ActualHigherSCoefficientBounds.exists_actual_first_coefficients_uniform_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2
  rcases hFirstFull with ⟨KF,hKF,hFirst⟩
  have hZeroFull := ActualHigherSZeroCoefficientBounds.exists_actual_zero_coefficient_uniform_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
  rcases hZeroFull with ⟨KZ,hKZ,hZero⟩
  have hAdjFull := ActualHigherSAdjointCoefficientBounds.exists_actual_adjoint_coefficient_uniform_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  rcases hAdjFull with ⟨KA,hKA,hAdj⟩
  let K := 1+KF+KZ+KA
  have hK : 0 ≤ K := add_nonneg (add_nonneg (add_nonneg zero_le_one hKF) hKZ) hKA
  have hFAsum : KF+KA ≤ K := by dsimp only [K]; linarith only [hKZ]
  have hZAsum : KZ+KA ≤ K := by dsimp only [K]; linarith only [hKF]
  refine ⟨K,hK,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq F0 hT hβ hsmall x
  by_cases hx : x ∈ TS F0
  · let r := referenceRadius δr Ar p L x
    let d : Fin 3 → Half := fun i => IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))
    let u := Uin F0 x
    have hmem := hT x hx
    have hFc := (hFirst δr Ar p hδr hAr q hq x hmem).1
    have hZc := hZero δr Ar p hδr hδr1 hAr hp q hq x hmem (hβ x hx) (hsmall x hx)
    have hAc := hAdj δr Ar p hδr hδr1 hAr hp q hq x hmem (hβ x hx) (hsmall x hx)
    have hf := ActualHigherSCoefficientExtraction.actual_higherS_frame_coefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x
    have ha := ActualHigherSAdjointCoefficientExtraction.actual_higherS_adjoint_frame_coefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hT x
    have hEvalF := norm_first_zero_apply_le (E := Half) (F := Hi) (V := Neg)
      (BF g2 δr Ar p q x) (CZ g2 δr Ar p q x) d u r KF KZ hFc hZc
    have hEvalA := norm_first_zero_apply_le (E := Half) (F := Hi) (V := Neg)
      (BA g2 δr Ar p q x) (CA g2 δr Ar p q x) d u r KA KA hAc.1 hAc.2
    have hfn : ‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x‖ ≤
        KF*r^2*(∑ i : Fin 3, ‖d i‖)+KZ*r*‖u‖ :=
      (congrArg (fun v : Neg => ‖v‖) hf).le.trans hEvalF
    have han : ‖JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ ≤
        KA*r^2*(∑ i : Fin 3, ‖d i‖)+KA*r*‖u‖ :=
      (congrArg (fun v : Neg => ‖v‖) ha).le.trans hEvalA
    have hds : 0 ≤ ∑ i : Fin 3, ‖d i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (d i))
    have hr0 : 0 ≤ r := le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)
    have hbound := add_two_weighted_bounds KF KZ KA KA K
      (r^2*(∑ i : Fin 3, ‖d i‖)) (r*‖u‖)
      (mul_nonneg (sq_nonneg r) hds) (mul_nonneg hr0 (norm_nonneg u)) hFAsum hZAsum
    have hnorm := (norm_add_le
      (NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x)
      (JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x))).trans (add_le_add hfn han)
    exact hnorm.trans (by simpa only [mul_assoc,firstZeroBaseEnergy,r,d,u] using hbound)
  · have hn := ActualHigherSCoefficientExtraction.nativeHigherSNegative_eq_zero_off_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x hx
    have ha := ActualHigherSAdjointFormation.higherSAdjointHalf_eq_zero_off_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x hx
    have hz : ‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x +
        JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ = 0 := by
      simp only [hn,ha,map_zero,zero_add,norm_zero]
    exact hz.le.trans (mul_nonneg hK (firstZeroBaseEnergy_nonneg g L hO hD δr Ar p q hδr hAr F0 x))

local notation "SH" => ActualHigherSFormation.nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "AO" => ActualHigherSAdjointFormation.higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact physical polarization for the original forward and adjoint Half fields. -/
theorem actual_higherS_physical_norm_difference (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ‖SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x‖^2 -
      ‖AO hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖^2 =
      sphereSobolevDualPairing (1/2 : ℝ)
        (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
        (NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)) := by
  have hOut := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 hg2 δr Ar p hδr hAr q hq F0 hT
  have hGraph : JL (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x) =
      NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x := hOut.2.2.2.1 x
  have hSum : JL (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x+
      ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
      NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) :=
    (map_add JL _ _).trans (congrArg (fun v : Neg => v+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)) hGraph)
  have hp := physical_norm_difference_of_graph hO hD
    (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x) (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
    (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
    (NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)) rfl hSum
  simpa only [ActualHigherSFormation.nativeHigherSOut,ActualHigherSAdjointFormation.higherSAdjointOut] using hp

/-- One constant controls the actual negative sum and reduces the original physical
signed norm comparison to the explicit actual Half difference. Sharp signed cancellation
remains separate; no gain of the entire raw difference is claimed. -/
theorem exists_actual_higherS_sum_physical_reduction (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
      ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, 1 ≤ actualReferenceBeta g L q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1) →
      ∀ x : R3,
      (‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+
        JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ ≤ K*E1 δr Ar p q F0 x) ∧
      |‖SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x‖^2 -
        ‖AO hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖^2| ≤
      ‖SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖ *
        (K*E1 δr Ar p q F0 x) := by
  have hFull := exists_actual_higherS_sum_negative_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac hL g2 hg2
  rcases hFull with ⟨K,hK,hBound⟩
  refine ⟨K,hK,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq F0 hT hβ hsmall x
  have hn := hBound δr Ar p hδr hδr1 hAr hp q hq F0 hT hβ hsmall x
  refine ⟨hn,?_⟩
  have he := actual_higherS_physical_norm_difference g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F0 hT x
  calc
    _ = |sphereSobolevDualPairing (1/2 : ℝ)
      (SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
      (NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x))| :=
        congrArg abs he
    _ ≤ ‖SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖ *
      ‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ :=
        abs_sphereSobolevDualPairing_le (1/2 : ℝ) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)

/-- Same original room on ANY W before g2/profiles/input, carrying both quantitative
negative sum and exact physical reduction with one profile-independent constant. -/
theorem exists_retained_actual_higherS_sum_control (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∃ hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z,
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, 1 ≤ actualReferenceBeta g L q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1) →
      ∀ x : R3,
      (‖NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x+
        JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x)‖ ≤ K*E1 δr Ar p q F0 x) ∧
      |‖SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x‖^2 -
        ‖AO hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖^2| ≤
      ‖SH δr Ar p hδr hAr q hreg δ0 W g2 F0 x-ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x‖ *
        (K*E1 δr Ar p q F0 x) := by
  have hFull := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,Cm,hJac⟩
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_higherS_sum_physical_reduction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac hL g2 hg2

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSumNegativeBounds
