import Calderon.ActualHigherSCoefficientExtraction
import Calderon.ReferenceWeightedApproximation
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoefficientBounds
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

private lemma norm_sum_three_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin 3 → ℝ) (v : Fin 3 → E) (A V : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i, |a i| ≤ A) (hv : ∀ i, ‖v i‖ ≤ V) :
    ‖∑ i : Fin 3, a i • v i‖ ≤ 3*A*V := by
  calc
    _ ≤ ∑ i : Fin 3, ‖a i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, A*V := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (ha i) (hv i) (norm_nonneg _) hA
    _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma norm_radius_sq_pair_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (a b : E) (A : ℝ) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) :
    ‖r^2 • a+r^2 • b‖ ≤ 2*A*r^2 := by
  calc
    _ ≤ ‖r^2 • a‖+‖r^2 • b‖ := norm_add_le _ _
    _ = r^2*‖a‖+r^2*‖b‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    _ ≤ r^2*A+r^2*A := add_le_add (mul_le_mul_of_nonneg_left ha (sq_nonneg r))
      (mul_le_mul_of_nonneg_left hb (sq_nonneg r))
    _ = _ := by ring

lemma norm_firstFrameCoefficient_le (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (CQ CE : ℝ) (hCQ : 0 ≤ CQ)
    (hQ : ∀ i j, |Q i j| ≤ CQ) (hE : ∀ j, ‖El j‖ ≤ CE) (m : Fin 3) :
    ‖ActualHigherSCoefficientExtraction.firstFrameCoefficient r Q El m‖ ≤
      6*CQ*CE*r^2 := by
  have h1 := norm_sum_three_smul_le (fun j => Q m j) El CQ CE hCQ (hQ m) hE
  have h2 := norm_sum_three_smul_le (fun i => Q i m) El CQ CE hCQ (fun i => hQ i m) hE
  have h := norm_radius_sq_pair_le r (∑ j : Fin 3, Q m j • El j)
    (∑ i : Fin 3, Q i m • El i) (3*CQ*CE) h1 h2
  exact h.trans_eq (by ring)

lemma norm_firstCoordinateCoefficient_le (B : Fin 3 → Half →L[ℝ] Neg)
    (X : Fin 3 → R3) (CX CB : ℝ) (hCX : 0 ≤ CX)
    (hX : ∀ m l, |X m l| ≤ CX) (hB : ∀ m, ‖B m‖ ≤ CB) (l : Fin 3) :
    ‖ActualHigherSCoefficientExtraction.firstCoordinateCoefficient B X l‖ ≤ 3*CX*CB :=
  norm_sum_three_smul_le (fun m => X m l) B CX CB hCX (fun m => hX m l) hB

/-- Original small-radius substitution for the coefficient weight. -/
lemma beta_mul_radius_sq_le (r β η : ℝ) (hr : 0 ≤ r) (hβ : 1 ≤ β)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hsmall : r*β^2 ≤ η) : β*r^2 ≤ η := by
  have hb0 : 0 ≤ β := le_trans zero_le_one hβ
  have hbb : β ≤ β^2 := by nlinarith
  have hbr : r*β ≤ η := (mul_le_mul_of_nonneg_left hbb hr).trans hsmall
  have hr1 : r ≤ 1 := by
    simpa only [mul_one] using ((mul_le_mul_of_nonneg_left hβ hr).trans hbr).trans hη1
  calc
    β*r^2 = r*(r*β) := by ring
    _ ≤ r*η := mul_le_mul_of_nonneg_left hbr hr
    _ ≤ η := by nlinarith


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
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
local notation "PL" => ActualHigherSCoefficientExtraction.profileLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BF" => ActualHigherSCoefficientExtraction.higherSFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BC" => ActualHigherSCoefficientExtraction.higherSFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow sphereSobolevInclusionL
 referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
 referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient

/-- The original lower quotient is the same continuous operator on ALL Half,
by the original dense Hi inclusion. No surjectivity or truncation is used. -/
theorem profileLow_eq_canonical (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) :
    PL δr Ar p q x j = EL j ((Tq δr Ar p q) x) := by
  have hr := ActualHigherSFormation.higherSRoomAt_of_mem_paramRoom hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q δ δ δ (le_refl _) (le_refl _) Cm.rev.room hJac x hx
  have ha : (fun v : Hi => PL δr Ar p q x j (IH v)) =
      (fun v : Hi => EL j ((Tq δr Ar p q) x) (IH v)) := by
    funext v
    exact (ActualHigherSFormation.lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ x hr j v).trans (Cm.compat j _ hx v)
  have hh := (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
    (PL δr Ar p q x j).continuous (EL j ((Tq δr Ar p q) x)).continuous ha
  apply ContinuousLinearMap.ext
  intro v
  exact congrFun hh v

/-- One operator bound on the compact original parameter room, before all profiles. -/
theorem exists_canonicalLow_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ CE : ℝ, 1 ≤ CE ∧ ∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ‖EL j t‖ ≤ CE := by
  classical
  have hK := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hs (j : Fin 3) : ContinuousOn (EL j) (ParamRoom δ) :=
    fun t ht => (Cm.germLow j t ht).continuousAt.continuousWithinAt
  have hb (j : Fin 3) : ∃ C : ℝ, ∀ t ∈ ParamRoom δ, ‖EL j t‖ ≤ C :=
    hK.exists_bound_of_continuousOn (f := EL j) (hs j)
  choose CE hCE using hb
  have h0 : 0 ≤ ∑ j : Fin 3, |CE j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨1+∑ j : Fin 3, |CE j|,by linarith,?_⟩
  intro j t ht
  apply (hCE j t ht).trans
  calc
    CE j ≤ |CE j| := le_abs_self _
    _ ≤ ∑ k : Fin 3, |CE k| := Finset.single_le_sum (f := fun k : Fin 3 => |CE k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ 1+∑ k : Fin 3, |CE k| := by linarith


private lemma compact_finite_family_bound {α E ι : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : ι, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : ι => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : ι, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : ι, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : ι, |C j| := Finset.single_le_sum (f := fun j : ι => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : ι, |C j| := by linarith

include hg in
/-- Fixed geometric principal/frame bounds, chosen before every profile. -/
theorem exists_principal_frame_uniform_bound (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
      ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M ∧
        |referenceMetricGramFrame g L (q,x) i j| ≤ M := by
  let K : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall y0 ρ)
  have hQ (z : Fin 3 × Fin 3) : ContinuousOn
      (fun t : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 z.1 z.2) K :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L z.1 z.2).continuous.continuousOn
  have hX (z : Fin 3 × Fin 3) : ContinuousOn
      (fun t : ℝ × R3 => referenceMetricGramFrame g L t z.1 z.2) K :=
    ((contDiff_piLp 2).1 (contDiff_referenceMetricGramFrame g hg L z.1) z.2).continuous.continuousOn
  obtain ⟨CQ,hCQ,hQc⟩ := compact_finite_family_bound K hK
    (fun z : Fin 3 × Fin 3 => fun t : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 z.1 z.2) hQ
  obtain ⟨CX,hCX,hXc⟩ := compact_finite_family_bound K hK
    (fun z : Fin 3 × Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t z.1 z.2) hX
  refine ⟨max CQ CX,hCQ.trans (le_max_left _ _),?_⟩
  intro q hq x hx i j
  exact ⟨by simpa only [Real.norm_eq_abs] using (hQc (i,j) (q,x) ⟨hq,hx⟩).trans (le_max_left CQ CX),
    by simpa only [Real.norm_eq_abs] using (hXc (i,j) (q,x) ⟨hq,hx⟩).trans (le_max_right CQ CX)⟩


/-- Uniform first-base coefficient bounds, with ONE K before every profile and input. -/
theorem exists_actual_first_coefficients_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      (∀ m : Fin 3, ‖BF g2 δr Ar p q x m‖ ≤ K*(referenceRadius δr Ar p L x)^2) ∧
      (∀ l : Fin 3, ‖BC g2 δr Ar p q x l‖ ≤ K*(referenceRadius δr Ar p L x)^2) := by
  obtain ⟨CE,hCE,hEc⟩ := exists_canonicalLow_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm
  obtain ⟨M,hM,hMc⟩ := exists_principal_frame_uniform_bound g L y0 ρ hg g2 hg2
  have hm0 : 0 ≤ M := le_trans zero_le_one hM
  have he0 : 0 ≤ CE := le_trans zero_le_one hCE
  let KF := 6*M*CE
  let KC := 18*M*M*CE
  have hf0 : 0 ≤ KF := by dsimp [KF]; positivity
  have hc0 : 0 ≤ KC := by dsimp [KC]; positivity
  refine ⟨KF+KC,add_nonneg hf0 hc0,?_⟩
  intro δr Ar p hδr hAr q hq x hx
  let r := referenceRadius δr Ar p L x
  let Q : Fin 3 → Fin 3 → ℝ := fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let E : Fin 3 → Half →L[ℝ] Neg := PL δr Ar p q x
  have hqmc := hMc q hq x hx.1.2.1
  have hQ (i j : Fin 3) : |Q i j| ≤ M := (hqmc i j).1
  have hX (i j : Fin 3) : |referenceMetricGramFrame g L (q,x) i j| ≤ M := (hqmc i j).2
  have hE (j : Fin 3) : ‖E j‖ ≤ CE := by
    have heq := profileLow_eq_canonical g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac δr Ar p hδr hAr q hq x hx j
    exact (congrArg (fun A : Half →L[ℝ] Neg => ‖A‖) heq).le.trans (hEc j _ hx)
  have hF (m : Fin 3) : ‖BF g2 δr Ar p q x m‖ ≤ KF*r^2 :=
    norm_firstFrameCoefficient_le r Q E M CE hm0 hQ hE m
  have hC (l : Fin 3) : ‖BC g2 δr Ar p q x l‖ ≤ KC*r^2 := by
    have h := norm_firstCoordinateCoefficient_le (BF g2 δr Ar p q x)
      (referenceMetricGramFrame g L (q,x)) M (KF*r^2) hm0 hX hF l
    exact h.trans_eq (by dsimp [KC,KF]; ring)
  exact ⟨fun m => (hF m).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc0) (sq_nonneg r)),
    fun l => (hC l).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf0) (sq_nonneg r))⟩

/-- SAME K with the original physical beta/radius substitution; a coefficient
estimate, not a signed norm bound or L2 output estimate. -/
theorem exists_actual_first_coordinate_small_profile_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1 → 1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ η →
      ∀ l : Fin 3, actualReferenceBeta g L q δr Ar p x*‖BC g2 δr Ar p q x l‖ ≤ K*η := by
  obtain ⟨K,hK,hcap⟩ := exists_actual_first_coefficients_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2
  refine ⟨K,hK,?_⟩
  intro δr Ar p hδr hAr q hq x hx η hη0 hη1 hβ hsmall l
  let β := actualReferenceBeta g L q δr Ar p x
  let r := referenceRadius δr Ar p L x
  have hr0 : 0 ≤ r := le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hb0 : 0 ≤ β := le_trans zero_le_one hβ
  have hs := beta_mul_radius_sq_le r β η hr0 hβ hη0 hη1 hsmall
  have hc := (hcap δr Ar p hδr hAr q hq x hx).2 l
  calc
    β*‖BC g2 δr Ar p q x l‖ ≤ β*(K*r^2) := mul_le_mul_of_nonneg_left hc hb0
    _ = K*(β*r^2) := by ring
    _ ≤ K*η := mul_le_mul_of_nonneg_left hs hK

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoefficientBounds
