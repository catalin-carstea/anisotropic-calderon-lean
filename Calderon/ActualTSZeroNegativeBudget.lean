import Calderon.ActualTSZeroWeightedScalar
import Calderon.ActualHigherSQuadraticZeroNegativeProfileGraphs

/-!
Original quadratic S forward/reverse negative-value budget, needed for the
retained raw T-adjoint correction. No quadratic Hi->Half cap is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroNegativeBudget
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualHigherSQuadraticZeroWords
  ActualHigherSQuadraticZeroNegativeGraphs ReferenceWeightedApproximation ReferenceDensityBounds
  ConformalDepth AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection

private lemma norm_weighted_composite_sum_le {E H N ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (c : ι → ℝ) (A : ι → H →L[ℝ] N) (B : ι → E →L[ℝ] H)
    (C r M : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hc : ∀ i, |c i| ≤ C*r) (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ i, ‖B i‖ ≤ M) (U : E) :
    ‖∑ i : ι, c i • A i (B i U)‖ ≤ (Fintype.card ι : ℝ)*C*r*M^2*‖U‖ := by
  have hrow (i : ι) : ‖c i • A i (B i U)‖ ≤ (C*r)*M^2*‖U‖ := by
    have hBU : ‖B i U‖ ≤ M*‖U‖ :=
      ((B i).le_opNorm U).trans (mul_le_mul_of_nonneg_right (hB i) (norm_nonneg U))
    have hAB : ‖A i (B i U)‖ ≤ M*(M*‖U‖) :=
      ((A i).le_opNorm _).trans (mul_le_mul (hA i) hBU (norm_nonneg _) hM)
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hc i) hAB (norm_nonneg _) (mul_nonneg hC hr)).trans_eq (by ring)
  calc
    _ ≤ ∑ i : ι, ‖c i • A i (B i U)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (C*r)*M^2*‖U‖ := Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

private lemma norm_weighted_composite_value_le {E H N ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (c : ι → ℝ) (A : ι → H →L[ℝ] N) (B : ι → E →L[ℝ] H)
    (C r M : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hc : ∀ i, |c i| ≤ C*r) (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ i, ‖B i‖ ≤ M)
    (U : E) (V : N) (hV : V = ∑ i : ι, c i • A i (B i U)) :
    ‖V‖ ≤ (Fintype.card ι : ℝ)*C*r*M^2*‖U‖ := by
  rw [hV]
  exact norm_weighted_composite_sum_le c A B C r M hC hr hM hc hA hB U

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d


local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "WC" => actualWordCoefficient g L
local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WQ" => quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WT" => quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Original forward negative value norm; a scalar elaboration boundary only. -/
def forwardQuadraticNegativeValueNorm (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (U : Hi) : ℝ := ‖WQ g2 dr Ar p q x U‖

/-- Original genuine reverse negative value norm, with identical inherited norm. -/
def reverseQuadraticNegativeValueNorm (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (U : Hi) : ℝ := ‖WT g2 dr Ar p q x U‖

local notation "NQ" => forwardQuadraticNegativeValueNorm
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "NT" => reverseQuadraticNegativeValueNorm
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] forwardQuadraticNegativeValueNorm reverseQuadraticNegativeValueNorm
  atomHigh atomLow atomReverseHigh atomReverseLow
  angularAtomHigh angularAtomLow angularAtomReverseHigh angularAtomReverseLow
  quadraticZeroNegative quadraticZeroReverseNegative

/-- Actual original negative maps: constant chosen from fixed room/scalar caps
before every later profile and input. Same original207 coefficients and Q orders. -/
theorem exists_original_quadratic_zero_negative_bound
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    {radius : ℝ} (P : ARoom radius) :
    ∃ Cneg : ℝ, 0 < Cneg ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ closedBall y0 ρ,
      (Tq dr Ar p q) x ∈ ParamRoom radius →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ 1 →
      ∀ U : Hi,
      NQ g2 dr Ar p q x U ≤ Cneg*referenceRadius dr Ar p L x*‖U‖ ∧
      NT g2 dr Ar p q x U ≤ Cneg*referenceRadius dr Ar p L x*‖U‖ := by
  let caps := P.finiteCaps 0
  let Mop := Classical.choose caps
  have hMop : 1 ≤ Mop := (Classical.choose_spec caps).1
  have hAtoms := (Classical.choose_spec caps).2.1
  obtain ⟨Msc,hMsc,hScalars⟩ :=
    ActualHigherSLinearZeroScalarCaps.exists_word_scalar_caps g hg L hL y0 ρ g2 hg2
  let Czero : ℝ := 207*Msc^2*Mop^2
  let Cneg : ℝ := 1+Czero
  have hMop0 : 0 ≤ Mop := zero_le_one.trans hMop
  have hZero : 0 ≤ Czero := by dsimp only [Czero]; positivity
  have hCneg : 0 < Cneg := by dsimp only [Cneg]; linarith only [hZero]
  have hCzero : Czero ≤ Cneg := by dsimp only [Cneg]; linarith
  refine ⟨Cneg,hCneg,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx ht hb hs U
  let t := (Tq dr Ar p q) x
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hsc := hScalars q hq dr hdr hdr1 Ar hAr p hp x hx hb
  have hGamma (i a b : Fin 3) :
      |ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t| ≤ Msc := by
    simpa only [ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
      ActualHigherSZeroCoefficientFactorisation.parameterGramFrame,
      ActualHigherSFormation.higherSParam,t] using hsc.2.1 i a b
  have hc (z : ZeroWord) : |WC g2 dr Ar p q x z| ≤ Msc^2*r :=
    ActualHigherSQuadraticZeroQuarticBounds.abs_wordCoefficient_le_common r beta Msc
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
      (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t)
      hr hb hMsc hs hsc.1 hsc.2.2.1 hGamma z
  have hAH (b : ZeroAtom) : ‖AH t b‖ ≤ Mop :=
    (congrArg (fun A : Hi →L[ℝ] Half => ‖A‖)
      (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (by
          simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).1)
  have hAL (b : ZeroAtom) : ‖AL t b‖ ≤ Mop :=
    (congrArg (fun A : Half →L[ℝ] Neg => ‖A‖)
      (ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (by
          simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.1)
  have hRH (b : ZeroAtom) : ‖RH t b‖ ≤ Mop :=
    (congrArg (fun A : Hi →L[ℝ] Half => ‖A‖)
      (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (by
          simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.2.1)
  have hRL (b : ZeroAtom) : ‖RL t b‖ ≤ Mop :=
    (congrArg (fun A : Half →L[ℝ] Neg => ‖A‖)
      (ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)).le.trans (by
          simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.2.2)
  have hPlus := norm_weighted_composite_value_le (WC g2 dr Ar p q x)
    (fun z : ZeroWord => AL t (wordAtoms z).1) (fun z : ZeroWord => AH t (wordAtoms z).2)
    (Msc^2) r Mop (sq_nonneg _) hr hMop0 hc
    (fun z => hAL (wordAtoms z).1) (fun z => hAH (wordAtoms z).2) U
    (WQ g2 dr Ar p q x U)
    (quadraticZeroNegative_apply_eq_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x U)
  have hMinus := norm_weighted_composite_value_le (WC g2 dr Ar p q x)
    (fun z : ZeroWord => RL t (wordAtoms z).2) (fun z : ZeroWord => RH t (wordAtoms z).1)
    (Msc^2) r Mop (sq_nonneg _) hr hMop0 hc
    (fun z => hRL (wordAtoms z).2) (fun z => hRH (wordAtoms z).1) U
    (WT g2 dr Ar p q x U)
    (quadraticZeroReverseNegative_apply_eq_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x U)
  rw [card_zeroWord] at hPlus hMinus
  have hscale : (207 : ℝ)*Msc^2*r*Mop^2*‖U‖ = Czero*r*‖U‖ := by
    dsimp only [Czero]
    ring
  have hFwd : ‖WQ g2 dr Ar p q x U‖ ≤ Czero*r*‖U‖ :=
    hPlus.trans_eq hscale
  have hRev : ‖WT g2 dr Ar p q x U‖ ≤ Czero*r*‖U‖ :=
    hMinus.trans_eq hscale
  unfold forwardQuadraticNegativeValueNorm reverseQuadraticNegativeValueNorm
  exact ⟨hFwd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCzero hr) (norm_nonneg _)),
    hRev.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCzero hr) (norm_nonneg _))⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroNegativeBudget
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroNegativeBudget.exists_original_quadratic_zero_negative_bound
