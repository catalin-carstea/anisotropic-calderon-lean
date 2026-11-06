import Calderon.ActualLowerUSDLowFinitePairing
import Calderon.ActualLowerUSSignedRows
import Calderon.ActualLowerUSFullFirstJets
import Calderon.ActualLowerUSZeroDerivativeGraph
import Calderon.ActualHigherSCoordinateWeightBounds
import Calderon.ActualHigherSZeroCoefficientFactorisation

/-! Actual ordinary R/Z products. Original native factories, true sphere adjoints,
all scalar terms, and original profile caps are retained.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSOrdinaryRows
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSFirstOutput ActualHigherSFirstPhysicalCommutatorGraph
  ActualHigherSFirstCoefficientJets ActualHigherSZeroPhysicalGraph ActualHigherSZeroCoefficientJets
  ActualHigherSPhysicalPairing ActualLowerUSSignedRows ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain ActualModelCommutatorWords ActualHigherSScalarCommutatorForm
  ActualHigherSZeroScalarCommutatorForm FixedParameterProfilePullback FixedParameterProfileBudgets
  PrincipalCommutator
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def ordinaryHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] ordinaryHighNormed
@[instance_reducible] private def ordinaryHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] ordinaryHighSpace
@[instance_reducible] private def ordinaryLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] ordinaryLowNormed
@[instance_reducible] private def ordinaryLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] ordinaryLowSpace
@[instance_reducible] private def ordinaryZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] ordinaryZeroNormed
@[instance_reducible] private def ordinaryZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] ordinaryZeroSpace

private theorem scaled_sum_low_adjoint {ι : Type*} [Fintype ι]
    (r : ℝ) (c : ι → ℝ) (A : ι → Half →L[ℝ] Neg) (Asharp : ι → Hi →L[ℝ] Half)
    (hA : ∀ i (u : Hi) (z : Half), PP (IH u) (A i z) = PP (Asharp i u) (JL z))
    (u : Hi) (z : Half) :
    PP (IH u) ((r • ∑ i : ι, c i • A i) z) =
      PP ((r • ∑ i : ι, c i • Asharp i) u) (JL z) := by
  have hP (i : ι) : ⟪IH u,A i z⟫_ℝ = ⟪Asharp i u,JL z⟫_ℝ := hA i u z
  simp only [smul_apply,sum_apply,sphereSobolevDualPairing,inner_sum,sum_inner,
    real_inner_smul_left,real_inner_smul_right]
  simp only [hP]

private theorem ordinary_contDiff_half_output
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : R3 → Half) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun x => sphereSobolevHalfToSphereL2L hO hD (v x)) :=
  (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hv

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)


local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)
local notation "Pout" g2:max dr:max Ar:max p:max q:max =>
  nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "PL" g2:max dr:max Ar:max p:max q:max =>
  canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "PH" g2:max dr:max Ar:max p:max q:max =>
  highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "QH" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "QL" g2:max dr:max Ar:max p:max q:max =>
  canonicalZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
private abbrev ordinaryFiniteWeightValue (s : ℝ) (F : FC) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "WH" F:max x:max => ‖ordinaryFiniteWeightValue hO hD (1/2 : ℝ) F x‖
local notation "WHi" F:max x:max => ‖ordinaryFiniteWeightValue hO hD (3/2 : ℝ) F x‖

/-- Genuine sphere adjoint of the actual P low coefficient, on high tests. -/
def actualFirstAdjointHigh (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (x : R3) : Hi →L[ℝ] Half :=
  (referenceRadius dr Ar p L x)^2 • (∑ a : Fin 3,
    firstCoordinateWeight g g2 L j a ((Tq dr Ar p q) x) • eH a ((Tq dr Ar p q) x))

private lemma actualE_low_adjoint (j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom data.δ) (u : Hi) (z : Half) :
    PP (IH u) (EL j t z) = PP (eH j t u) (JL z) := by
  have ht0 : t ∈ ParamRoom data.δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  have hp := (data.germs.piGerm j t ht0).self_of_nhds
  let Q := piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    data.δ0 data.germs j t
  have hPair := canonicalLow_explicit_ordered_reverse_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 (IH u) z
  have hCompat := explicit_ordered_reverse_high_low_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 u
  calc
    _ = PP z (eL j t (IH u)) := hPair
    _ = PP z (JL (eH j t u)) := congrArg (PP z) hCompat.symm
    _ = PP (eH j t u) (JL z) := by
      rw [halfPairing_eq_inner_sphereL2 hO hD,halfPairing_eq_inner_sphereL2 hO hD]
      exact real_inner_comm _ _

/-- Actual P-low adjunction against every Half input. -/
theorem actualFirstAdjointHigh_pairing (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (u : Hi) (z : Half) :
    PP (IH u) ((PL g2 dr Ar p q) x j z) =
      PP (actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q j x u) (JL z) := by
  unfold canonicalFirstCoordinateCoefficient actualFirstAdjointHigh
  rw [firstCoordinateFactor_eq_contracted]
  exact scaled_sum_low_adjoint ((referenceRadius dr Ar p L x)^2)
    (fun a : Fin 3 => firstCoordinateWeight g g2 L j a ((Tq dr Ar p q) x))
    (fun a : Fin 3 => EL a ((Tq dr Ar p q) x))
    (fun a : Fin 3 => eH a ((Tq dr Ar p q) x))
    (fun ia u z => actualE_low_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data ia _ hx u z) u z

/-- Literal physical first output paired through its actual high adjoint. -/
theorem nativeFirstOut_adjoint_pairing
    (δ : ℝ) (Cm : CRoom δ) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (U V : FC) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (hxE : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    ⟪U.val x,(Pout g2 dr Ar p q) j V x⟫_ℝ =
      PP (actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q j x (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (finiteCoreSobolevLift hO hD (-(1/2 : ℝ)) V x) := by
  have hGraph := highFirstCoordinateCoefficient_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 dr Ar p q j x hx
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)
  have hPhysical := finiteCore_halfPairing_eq_inner hO hD U
    ((PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) x
  simp only [sphereSobolevInclusionL_finiteCoreSobolevLift] at hPhysical
  have hPair := (congrArg (fun z : Neg =>
    PP (finiteCoreSobolevLift hO hD (1/2 : ℝ) U x) z) hGraph).symm.trans hPhysical
  simp only [sphereSobolevInclusionL_finiteCoreSobolevLift] at hPair
  have hAdj := actualFirstAdjointHigh_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 dr Ar p q j x hxE (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)
      (finiteCoreSobolevLift hO hD (1/2 : ℝ) V x)
  simp only [sphereSobolevInclusionL_finiteCoreSobolevLift] at hAdj
  have hOut : (Pout g2 dr Ar p q) j V x =
      sphereSobolevHalfToSphereL2L hO hD
        ((PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
    simp only [ActualLowerUSFirstOutput.nativeFirstOut]
  have hOutPair := congrArg (fun z : SphereL2 => ⟪U.val x,z⟫_ℝ) hOut
  have hBack := Eq.symm hPair
  have hCombined := Eq.trans hBack hAdj
  have hResult := Eq.trans hOutPair hCombined
  exact hResult


/-- A fixed finite-family norm estimate. The original producer below supplies
both scalar weights and actual reverse endpoint caps internally. -/
private lemma norm_actualFirstAdjointHigh_le (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (x : R3) (MW : ℝ)
    (hW : ∀ a : Fin 3, |firstCoordinateWeight g g2 L j a ((Tq dr Ar p q) x)| ≤ MW)
    (hE : ∀ a : Fin 3, ‖eH a ((Tq dr Ar p q) x)‖ ≤ data.M) :
    ‖actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q j x‖ ≤ (3*MW*data.M)*(referenceRadius dr Ar p L x)^2 := by
  unfold actualFirstAdjointHigh
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hSum : ‖∑ a : Fin 3, firstCoordinateWeight g g2 L j a ((Tq dr Ar p q) x) •
      eH a ((Tq dr Ar p q) x)‖ ≤ 3*(MW*data.M) := by
    calc
      _ ≤ ∑ a : Fin 3, ‖firstCoordinateWeight g g2 L j a ((Tq dr Ar p q) x) •
        eH a ((Tq dr Ar p q) x)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin 3, MW*data.M := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hW a) (hE a) (norm_nonneg _) (le_trans (abs_nonneg _) (hW a))
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hSum (sq_nonneg _)).trans_eq (by ring)

private lemma fderiv_fixed_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (f : R3 → E) (x X : R3) (hf : DifferentiableAt ℝ f x) :
    directionalFDeriv X (fun y => A (f y)) x = A (directionalFDeriv X f x) := by
  simpa only [directionalFDeriv,ContinuousLinearMap.comp_apply,Function.comp_def] using
    congrArg (fun D : R3 →L[ℝ] F => D X) (A.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- Differentiate a genuine global finite graph and subtract the actual input
term. This is a local calculus identity, with no endpoint-norm premise. -/
private lemma derivative_finite_graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u du : R3 → E) (a da : R3 → Half) (C : R3 → E →L[ℝ] Neg)
    (X x : R3) (hu : ContDiff ℝ ∞ u) (ha : ContDiff ℝ ∞ a)
    (hC : ContDiffAt ℝ ∞ C x)
    (hdu : directionalFDeriv X u x = du x)
    (hGraph : ∀ y, JL (a y) = C y (u y))
    (hGraphD : JL (da x) = C x (du x)) :
    JL (directionalFDeriv X a x-da x) =
      directionalFDeriv X C x (u x) := by
  have heq : (fun y => JL (a y)) = (fun y => C y (u y)) := funext hGraph
  have hd := congrArg (fun f : R3 → Neg => directionalFDeriv X f x) heq
  rw [fderiv_fixed_clm JL a x X (ha.differentiable (by simp) x)] at hd
  unfold directionalFDeriv at hd
  rw [fderiv_clm_apply (hC.differentiableAt (by simp)) (hu.differentiable (by simp) x)] at hd
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hd
  change JL (directionalFDeriv X a x) = C x (directionalFDeriv X u x)+
    directionalFDeriv X C x (u x) at hd
  rw [hdu] at hd
  have hSub := map_sub JL (directionalFDeriv X a x) (da x)
  have hReplace := congrArg₂ (fun a b : Neg => a-b) hd hGraphD
  have hCancel := add_sub_cancel_left (C x (du x)) (directionalFDeriv X C x (u x))
  have hValues := Eq.trans hReplace hCancel
  exact Eq.trans hSub hValues

private lemma firstHalf_smooth (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (fun x => (PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) := by
  exact contDiff_supported_operator_apply
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F)
    (fun x => (PH g2 dr Ar p q) x j) (tsupport F.val) (isClosed_tsupport _)
    (contDiff_finiteCoreSobolevLift hO hD _ F)
    (higherSInput_eq_zero_off hO hD F)
    (fun x hx => contDiffAt_highFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q j x (hTF x hx))

private lemma firstHalf_finite_negative_graph (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    JL ((PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
      (PL g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) := by
  by_cases hx : x ∈ tsupport F.val
  · have h := highFirstCoordinateCoefficient_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm g2 dr Ar p q j x (hTF x hx)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
    rw [sphereSobolevInclusionL_finiteCoreSobolevLift] at h
    exact h
  · have hh : finiteCoreSobolevLift hO hD (1/2 : ℝ) F x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hy => hx
        ((finiteCoreSobolevLift_representation hO hD (1/2 : ℝ) (by norm_num) F).2.2.1 hy))
    have hi := higherSInput_eq_zero_off hO hD F x hx
    simp only [ActualHigherSFormation.higherSInput] at hi
    simp only [hi,hh,map_zero]

/-- Actual Half realization of the literal P coefficient derivative. -/
def nativeDerivativePHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (i j : Fin 3) (F : FC) (x : R3) : Half :=
  directionalFDeriv (coordinateDirection i)
    (fun y => (PH g2 dr Ar p q) y j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)) x-
      (PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) ((dd i) F) x)

/-- Literal physical coefficient derivative and its genuine Half realization. -/
theorem nativeDerivativePOutput_eq_half (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    nativeDerivativePOutput g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i j F x = sphereSobolevHalfToSphereL2L hO hD
        (nativeDerivativePHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 dr Ar p q i j F x) := by
  have hSmooth := firstHalf_smooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data δ Cm g2 hg2 dr Ar p hdr hAr q j F hTF
  unfold nativeDerivativePOutput nativeFirstOut nativeDerivativePHalf
  rw [fderiv_fixed_clm (sphereSobolevHalfToSphereL2L hO hD) _ x (coordinateDirection i)
    (hSmooth.differentiable (by simp) x),map_sub]

/-- Exact full negative-space graph of the original dP output. -/
theorem nativeDerivativePHalf_negative_graph (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom δ) :
    JL (nativeDerivativePHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i j F x) =
      directionalFDeriv (coordinateDirection i) (fun y => (PL g2 dr Ar p q) y j) x
        (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) := by
  have hTDF : ∀ y ∈ tsupport ((dd i) F).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTF y ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F) hy)
  have hDerived := derivative_finite_graph
    (finiteCoreSobolevLift hO hD (1/2 : ℝ) F)
    (finiteCoreSobolevLift hO hD (1/2 : ℝ) ((dd i) F))
    (fun y => (PH g2 dr Ar p q) y j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    (fun y => (PH g2 dr Ar p q) y j (finiteCoreSobolevLift hO hD (3/2 : ℝ) ((dd i) F) y))
    (fun y => (PL g2 dr Ar p q) y j) (coordinateDirection i) x
    (contDiff_finiteCoreSobolevLift hO hD (1/2 : ℝ) F)
    (firstHalf_smooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data δ Cm g2 hg2 dr Ar p hdr hAr q j F hTF)
    (contDiffAt_canonicalFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q x hx j)
    (directionalFDeriv_finiteCoreSobolevLift hO hD (1/2 : ℝ) F (coordinateDirection i) x)
    (firstHalf_finite_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 dr Ar p q j F hTF)
    (firstHalf_finite_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 dr Ar p q j ((dd i) F) hTDF x)
  have hOutput : nativeDerivativePHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i j F x =
      directionalFDeriv (coordinateDirection i)
        (fun y => (PH g2 dr Ar p q) y j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)) x-
        (PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) ((dd i) F) x) := by
    simp only [nativeDerivativePHalf]
  have hLiftOutput := congrArg JL hOutput
  have hResult := Eq.trans hLiftOutput hDerived
  exact hResult

/-- Actual Half realization of the literal Q coefficient derivative. -/
def nativeDerivativeQHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (i : Fin 3) (F : FC) (x : R3) : Half :=
  directionalFDeriv (coordinateDirection i) ((QH g2 dr Ar p hdr hAr q) F) x-
    (QH g2 dr Ar p hdr hAr q) ((dd i) F) x

/-- Physical dQ decoding, retaining every original zero-coefficient field. -/
theorem nativeDerivativeQOutput_eq_half (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    nativeDerivativeQOutput g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i F x = sphereSobolevHalfToSphereL2L hO hD
        (nativeDerivativeQHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data g2 dr Ar p hdr hAr q i F x) := by
  have hSmooth := (nativeZeroHalf_regular
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF).1
  unfold nativeDerivativeQOutput nativeZeroOut nativeDerivativeQHalf
  rw [fderiv_fixed_clm (sphereSobolevHalfToSphereL2L hO hD) _ x (coordinateDirection i)
    (hSmooth.differentiable (by simp) x),map_sub]

/-- Literal original finite high input in the genuine Q negative graph. -/
private theorem zeroHalf_finite_negative_graph (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : FC) (hTF : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom δ) (x : R3) :
    JL ((QH g2 dr Ar p hdr hAr q) F x) =
      (QL g2 dr Ar p q) x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  have hRaw := nativeZeroHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF x
  have hInput : ActualHigherSFormation.higherSInput hO hD F x =
      finiteCoreSobolevLift hO hD (3/2 : ℝ) F x := by
    simp only [ActualHigherSFormation.higherSInput]
  have hInputMap := congrArg ((QL g2 dr Ar p q) x) hInput
  have hResult := Eq.trans hRaw hInputMap
  exact hResult

/-- Exact negative-space dQ graph; no angular finite-output substitution. -/
theorem nativeDerivativeQHalf_negative_graph (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom δ) :
    JL (nativeDerivativeQHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i F x) =
      directionalFDeriv (coordinateDirection i) (fun y => (QL g2 dr Ar p q) y) x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) := by
  have hTDF : ∀ y ∈ tsupport ((dd i) F).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTF y ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F) hy)
  have hDerived := derivative_finite_graph
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) ((dd i) F))
    ((QH g2 dr Ar p hdr hAr q) F) ((QH g2 dr Ar p hdr hAr q) ((dd i) F))
    ((QL g2 dr Ar p q)) (coordinateDirection i) x
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F)
    (nativeZeroHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF).1
    (contDiffAt_canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q x hx)
    (directionalFDeriv_finiteCoreSobolevLift hO hD (3/2 : ℝ) F (coordinateDirection i) x)
    (zeroHalf_finite_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF)
    (zeroHalf_finite_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq ((dd i) F) hTDF x)
  have hOutput : nativeDerivativeQHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i F x =
      directionalFDeriv (coordinateDirection i) ((QH g2 dr Ar p hdr hAr q) F) x-
        (QH g2 dr Ar p hdr hAr q) ((dd i) F) x := by
    simp only [nativeDerivativeQHalf]
  have hLiftOutput := congrArg JL hOutput
  have hResult := Eq.trans hLiftOutput hDerived
  exact hResult

/-- Bilinear version of the literal ordinary R row, with V replacing dd_j F. -/
def nativeOrdinaryRProduct (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (U V : FC) (x : R3) : ℝ :=
  ⟪-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x,
    nativeDerivativePOutput g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i j V x⟫_ℝ-
  ⟪U.val x,(Pout g2 dr Ar p q) i
    (coefficientDerivative (dd i)
      (nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j) V) x⟫_ℝ

/-- Bilinear version of the literal ordinary Z row. -/
def nativeOrdinaryZProduct (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i : Fin 3) (U V : FC) (x : R3) : ℝ :=
  ⟪-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x,
    nativeDerivativeQOutput g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i V x⟫_ℝ-
  ⟪U.val x,(Pout g2 dr Ar p q) i
    (coefficientDerivative (dd i)
      (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) V) x⟫_ℝ

/-- The bilinear R product specializes to the already fixed literal row. -/
theorem nativeOrdinaryRProduct_dd_eq_row (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (F : FC) (x : R3) :
    nativeOrdinaryRProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q i j F ((dd j) F) x =
    nativeOrdinaryRRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q i j F x := rfl

theorem nativeOrdinaryZProduct_self_eq_row (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i : Fin 3) (F : FC) (x : R3) :
    nativeOrdinaryZProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q i F F x =
    nativeOrdinaryZRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q i F x := rfl

/-- Exact before-profile ordinary-row target. Its explicit body records every
original cap hypothesis and both actual finite orientations used downstream. -/
def NativeOrdinaryRowsUniformProfileBound (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Prop :=
  ∃ δ : ℝ, ∃ Cm : CRoom δ,
    (∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
    ∃ COrd : ℝ, 0 < COrd ∧ ∃ etaOrd : ℝ, 0 < etaOrd ∧
      etaOrd ≤ data.eta0 ∧ etaOrd ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaOrd →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
      (∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom δ) ∧
      ∀ U V : FC, tsupport U.val ⊆ K → tsupport V.val ⊆ K →
      ∀ i j : Fin 3, ∀ x ∈ K,
        |nativeOrdinaryRProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 hg2 dr Ar p hdr hAr q i j U V x| ≤ COrd*eta*(WHi U x)*(WH V x) ∧
        |nativeOrdinaryZProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data g2 hg2 dr Ar p hdr hAr q i U V x| ≤
            COrd*eta*actualReferenceBeta g L q dr Ar p x*(WHi U x)*(WHi V x)

/-- Exact weak graph for D dP-P dD; the second coefficient derivative is
paired through the actual Pstar high map, without a negative-space product. -/
theorem nativeOrdinaryRProduct_weak_graph
    (δ : ℝ) (Cm : CRoom δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (U V : FC)
    (hTV : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (hxE : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    nativeOrdinaryRProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q i j U V x =
      PP (finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x)
        (directionalFDeriv (coordinateDirection i) (fun y => (PL g2 dr Ar p q) y j) x
          (finiteCoreSobolevLift hO hD (1/2 : ℝ) V x))-
      PP (actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (directionalFDeriv (coordinateDirection i)
          (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x
            (finiteCoreSobolevLift hO hD (1/2 : ℝ) V x)) := by
  have hP := nativeDerivativePOutput_eq_half
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm g2 hg2 dr Ar p hdr hAr q i j V hTV x
  have hGraph := nativeDerivativePHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm g2 hg2 dr Ar p hdr hAr q i j V hTV x hx
  have hPair := finiteCore_halfPairing_eq_inner hO hD
    (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U))
    (nativeDerivativePHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i j V x) x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift,hGraph] at hPair
  have hSecond := nativeFirstOut_adjoint_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm g2 dr Ar p q i U
    (coefficientDerivative (dd i)
      (nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j) V)
    x hx hxE
  rw [← lowerAdjointFirstLow_coefficientDerivative_finite_graph
    hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i j V x] at hSecond
  have hNegative :
      (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)).val x =
      -(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x := by
    simp only [Submodule.coe_neg,Pi.neg_apply]
  have hNegativePair := congrArg (fun z : SphereL2 =>
    ⟪z,sphereSobolevHalfToSphereL2L hO hD
      (nativeDerivativePHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q i j V x)⟫_ℝ) hNegative
  have hOutputPair := congrArg (fun z : SphereL2 =>
    ⟪-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x,z⟫_ℝ) hP
  have hPhysical := Eq.trans (Eq.symm hNegativePair) (Eq.symm hPair)
  have hFirst := Eq.trans hOutputPair hPhysical
  have hProduct := congrArg₂ (fun a b : ℝ => a-b) hFirst hSecond
  simpa only [nativeOrdinaryRProduct] using hProduct

/-- Exact weak graph for D dQ-P dJ. The dJ negative graph is used at its full
endpoint, so the actual Pstar test is not required to be angularly finite. -/
theorem nativeOrdinaryZProduct_weak_graph
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) (U V : FC)
    (hTV : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (hxE : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    nativeOrdinaryZProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q i U V x =
      PP (finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x)
        (directionalFDeriv (coordinateDirection i) ((QL g2 dr Ar p q)) x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x))-
      PP (actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (nativeULowerAdjointZeroDerivativeSobolev hO hD hF g g2 hg L q dr Ar p i x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
  have hQ := nativeDerivativeQOutput_eq_half
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq i V hTV x
  have hGraph := nativeDerivativeQHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq i V hTV x hx
  have hPair := finiteCore_halfPairing_eq_inner hO hD
    (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U))
    (nativeDerivativeQHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i V x) x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift,hGraph] at hPair
  have hSecond := nativeFirstOut_adjoint_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm g2 dr Ar p q i U
    (coefficientDerivative (dd i)
      (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) V)
    x hx hxE
  rw [← nativeULowerAdjointZeroDerivativeSobolev_negative_graph
    hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i V x] at hSecond
  have hNegative :
      (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)).val x =
      -(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x := by
    simp only [Submodule.coe_neg,Pi.neg_apply]
  have hNegativePair := congrArg (fun z : SphereL2 =>
    ⟪z,sphereSobolevHalfToSphereL2L hO hD
      (nativeDerivativeQHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p hdr hAr q i V x)⟫_ℝ) hNegative
  have hOutputPair := congrArg (fun z : SphereL2 =>
    ⟪-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U).val x,z⟫_ℝ) hQ
  have hPhysical := Eq.trans (Eq.symm hNegativePair) (Eq.symm hPair)
  have hFirst := Eq.trans hOutputPair hPhysical
  have hProduct := congrArg₂ (fun a b : ℝ => a-b) hFirst hSecond
  simpa only [nativeOrdinaryZProduct] using hProduct

private theorem operator_pair_cap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Half) (A : E →L[ℝ] Neg) (v : E) (a b c : ℝ)
    (hu : ‖u‖ ≤ a) (hA : ‖A‖ ≤ b) (hv : ‖v‖ ≤ c) :
    |PP u (A v)| ≤ a*b*c := by
  have ha : 0 ≤ a := (norm_nonneg u).trans hu
  have hb : 0 ≤ b := (norm_nonneg A).trans hA
  have hAv : ‖A v‖ ≤ b*c :=
    (A.le_opNorm v).trans (mul_le_mul hA hv (norm_nonneg v) hb)
  calc
    |PP u (A v)| ≤ ‖u‖*‖A v‖ := abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ a*(b*c) := mul_le_mul hu hAv (norm_nonneg (A v)) ha
    _ = a*b*c := (mul_assoc a b c).symm

private theorem operator_pair_cap_half
    (u : Half) (A : Half →L[ℝ] Neg) (v : Half) (a b c : ℝ)
    (hu : ‖u‖ ≤ a) (hA : ‖A‖ ≤ b) (hv : ‖v‖ ≤ c) :
    |PP u (A v)| ≤ a*b*c :=
  operator_pair_cap u A v a b c hu hA hv

private theorem operator_pair_cap_high
    (u : Half) (A : Hi →L[ℝ] Neg) (v : Hi) (a b c : ℝ)
    (hu : ‖u‖ ≤ a) (hA : ‖A‖ ≤ b) (hv : ‖v‖ ≤ c) :
    |PP u (A v)| ≤ a*b*c :=
  operator_pair_cap u A v a b c hu hA hv

private theorem ordinary_product_caps
    (uB uP : Half) (AP AD : Half →L[ℝ] Neg) (AQ AJ : Hi →L[ℝ] Neg)
    (vh : Half) (vhi : Hi) (CB CP CS CD CQ CJ eta wU wH wHi beta R Z : ℝ)
    (hCB : 0 ≤ CB) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCD : 0 ≤ CD)
    (hCQ : 0 ≤ CQ) (hCJ : 0 ≤ CJ) (heta : 0 ≤ eta)
    (hwU : 0 ≤ wU) (hwH : 0 ≤ wH) (hwHi : 0 ≤ wHi) (hb : 1 ≤ beta)
    (huB : ‖uB‖ ≤ CB*eta*wU) (huP : ‖uP‖ ≤ CS*wU)
    (hAP : ‖AP‖ ≤ CP) (hAD : ‖AD‖ ≤ CD*eta)
    (hAQ : ‖AQ‖ ≤ CQ) (hAJ : ‖AJ‖ ≤ CJ*eta*beta)
    (hvh : ‖vh‖ ≤ wH) (hvhi : ‖vhi‖ ≤ wHi)
    (hR : R = PP uB (AP vh)-PP uP (AD vh))
    (hZ : Z = PP uB (AQ vhi)-PP uP (AJ vhi)) :
    |R| ≤ (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*wU*wH ∧
    |Z| ≤ (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*beta*wU*wHi := by
  let C := 1+CB*CP+CS*CD+CB*CQ+CS*CJ
  have hRP := operator_pair_cap_half uB AP vh (CB*eta*wU) CP wH huB hAP hvh
  have hRD := operator_pair_cap_half uP AD vh (CS*wU) (CD*eta) wH huP hAD hvh
  have hZQ := operator_pair_cap_high uB AQ vhi (CB*eta*wU) CQ wHi huB hAQ hvhi
  have hZJ := operator_pair_cap_high uP AJ vhi (CS*wU) (CJ*eta*beta) wHi huP hAJ hvhi
  have hRcoeff : CB*CP+CS*CD ≤ C := by
    have hOther := add_nonneg (mul_nonneg hCB hCQ) (mul_nonneg hCS hCJ)
    dsimp only [C]
    linarith only [hOther]
  have hZcoeff : CB*CQ+CS*CJ ≤ C := by
    have hOther := add_nonneg (mul_nonneg hCB hCP) (mul_nonneg hCS hCD)
    dsimp only [C]
    linarith only [hOther]
  have hTriangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [Real.norm_eq_abs] using (norm_sub_le a b)
  constructor
  · calc
      |R| = |PP uB (AP vh)-PP uP (AD vh)| := congrArg abs hR
      _ ≤ |PP uB (AP vh)|+|PP uP (AD vh)| := hTriangle _ _
      _ ≤ (CB*eta*wU)*CP*wH+(CS*wU)*(CD*eta)*wH := add_le_add hRP hRD
      _ = (CB*CP+CS*CD)*(eta*wU*wH) := by ring
      _ ≤ C*(eta*wU*wH) := mul_le_mul_of_nonneg_right hRcoeff
        (mul_nonneg (mul_nonneg heta hwU) hwH)
      _ = (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*wU*wH := by dsimp only [C]; ring
  · have hFirstNonneg : 0 ≤ (CB*eta*wU)*CQ*wHi :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCB heta) hwU) hCQ) hwHi
    have hFirstBeta : (CB*eta*wU)*CQ*wHi ≤ ((CB*eta*wU)*CQ*wHi)*beta :=
      le_mul_of_one_le_right hFirstNonneg hb
    have hb0 : 0 ≤ beta := zero_le_one.trans hb
    calc
      |Z| = |PP uB (AQ vhi)-PP uP (AJ vhi)| := congrArg abs hZ
      _ ≤ |PP uB (AQ vhi)|+|PP uP (AJ vhi)| := hTriangle _ _
      _ ≤ (CB*eta*wU)*CQ*wHi+(CS*wU)*(CJ*eta*beta)*wHi := add_le_add hZQ hZJ
      _ ≤ ((CB*eta*wU)*CQ*wHi)*beta+(CS*wU)*(CJ*eta*beta)*wHi :=
        add_le_add hFirstBeta (le_refl _)
      _ = (CB*CQ+CS*CJ)*(eta*beta*wU*wHi) := by ring
      _ ≤ C*(eta*beta*wU*wHi) := mul_le_mul_of_nonneg_right hZcoeff
        (mul_nonneg (mul_nonneg (mul_nonneg heta hb0) hwU) hwHi)
      _ = (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*beta*wU*wHi := by dsimp only [C]; ring

private lemma abs_sub_le_add_abs (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [Real.norm_eq_abs] using (norm_sub_le a b)

private lemma abs_pair_operator (u : Half) (A : Half →L[ℝ] Neg) (v : Half) :
    |PP u (A v)| ≤ ‖u‖*‖A‖*‖v‖ := by
  exact (abs_sphereSobolevDualPairing_le _ _ _).trans
    ((mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u)).trans_eq (by ring))

private lemma abs_pair_operator_high (u : Half) (A : Hi →L[ℝ] Neg) (v : Hi) :
    |PP u (A v)| ≤ ‖u‖*‖A‖*‖v‖ := by
  exact (abs_sphereSobolevDualPairing_le _ _ _).trans
    ((mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u)).trans_eq (by ring))

private lemma norm_coordinate_derivative_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : R3 → E) (x : R3) (i : Fin 3) :
    ‖directionalFDeriv (coordinateDirection i) f x‖ ≤ ‖fderiv ℝ f x‖ := by
  have hn : ‖coordinateDirection i‖ = 1 := by simp [coordinateDirection]
  exact ((fderiv ℝ f x).le_opNorm (coordinateDirection i)).trans_eq (by rw [hn,mul_one])

private theorem nativeOrdinaryProducts_bound_of_actual_caps
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) (i j : Fin 3) (U V : FC)
    (hTV : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (hxE : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (CB CP CS CD CQ CJ eta : ℝ)
    (hCB : 0 ≤ CB) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCD : 0 ≤ CD)
    (hCQ : 0 ≤ CQ) (hCJ : 0 ≤ CJ) (heta : 0 ≤ eta)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hBN : ‖finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x‖ ≤ CB*eta*(WHi U x))
    (hPS : ‖actualFirstAdjointHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i x‖ ≤ CS)
    (hPDerivative : ‖directionalFDeriv (coordinateDirection i)
      (fun y => (PL g2 dr Ar p q) y j) x‖ ≤ CP)
    (hDDerivative : ‖directionalFDeriv (coordinateDirection i)
      (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x‖ ≤ CD*eta)
    (hQDerivative : ‖directionalFDeriv (coordinateDirection i) ((QL g2 dr Ar p q)) x‖ ≤ CQ)
    (hJDerivative : ‖nativeULowerAdjointZeroDerivativeSobolev
      hO hD hF g g2 hg L q dr Ar p i x‖ ≤ CJ*eta*actualReferenceBeta g L q dr Ar p x) :
    |nativeOrdinaryRProduct
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q i j U V x| ≤
        (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*(WHi U x)*(WH V x) ∧
    |nativeOrdinaryZProduct
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q i U V x| ≤
        (1+CB*CP+CS*CD+CB*CQ+CS*CJ)*eta*actualReferenceBeta g L q dr Ar p x*(WHi U x)*(WHi V x) := by
  have huN : ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) U x‖ = WHi U x :=
    norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) U x
  have hInputScaled := congrArg (fun z : ℝ => CS*z) huN
  have hMapScaled := mul_le_mul_of_nonneg_right hPS
    (norm_nonneg (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
  have hPSu := ((actualFirstAdjointHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 dr Ar p q i x).le_opNorm
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)).trans
        (hMapScaled.trans_eq hInputScaled)
  have hvhN : ‖finiteCoreSobolevLift hO hD (1/2 : ℝ) V x‖ = WH V x :=
    norm_finiteCoreSobolevLift hO hD (1/2 : ℝ) V x
  have hvN : ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) V x‖ = WHi V x :=
    norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) V x
  have hwU : 0 ≤ WHi U x :=
    (norm_nonneg (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)).trans_eq huN
  have hwH : 0 ≤ WH V x :=
    (norm_nonneg (finiteCoreSobolevLift hO hD (1/2 : ℝ) V x)).trans_eq hvhN
  have hwHi : 0 ≤ WHi V x :=
    (norm_nonneg (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)).trans_eq hvN
  have hRGraph := nativeOrdinaryRProduct_weak_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm g2 hg2 dr Ar p hdr hAr q i j U V hTV x hx hxE
  have hZGraph := nativeOrdinaryZProduct_weak_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq i U V hTV x hx hxE
  have hCaps := ordinary_product_caps
    (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x)
    (actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
    (directionalFDeriv (coordinateDirection i) (fun y => (PL g2 dr Ar p q) y j) x)
    (directionalFDeriv (coordinateDirection i)
      (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x)
    (directionalFDeriv (coordinateDirection i) ((QL g2 dr Ar p q)) x)
    (nativeULowerAdjointZeroDerivativeSobolev hO hD hF g g2 hg L q dr Ar p i x)
    (finiteCoreSobolevLift hO hD (1/2 : ℝ) V x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)
    CB CP CS CD CQ CJ eta (WHi U x) (WH V x) (WHi V x)
    (actualReferenceBeta g L q dr Ar p x)
    (nativeOrdinaryRProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q i j U V x)
    (nativeOrdinaryZProduct g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q i U V x)
    hCB hCP hCS hCD hCQ hCJ heta hwU hwH hwHi hb
    hBN hPSu hPDerivative hDDerivative hQDerivative hJDerivative hvhN.le hvN.le hRGraph hZGraph
  exact hCaps

/-- All four ordinary products, with their actual maps and original cap
producers. Constants follow fixed g2 and precede q, every profile and input. -/
theorem exists_nativeOrdinaryRows_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    NativeOrdinaryRowsUniformProfileBound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaF,hEtaF,hEtaF1,hGuardF⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ δ Cm.rev.pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaD,hEtaD,hEtaD1,hGuardD⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ data.δ data.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨CB,hCB,hBCap⟩ := exists_nativeULowerAdjointFirst_uniform_half_norm_bounds
    hO hD hF g g2 hg hg2 L hL y0 ρ
  obtain ⟨CD,hCD,hDCap⟩ := exists_lowerAdjointFirstLow_uniform_word_bound
    hF hO hD g g2 hg hg2 L hL y0 ρ
  obtain ⟨CJ,hCJ,hJCap⟩ := exists_nativeULowerAdjointZeroDerivativeSobolev_uniform_bound
    hO hD hF g g2 hg hg2 L hL y0 ρ
  obtain ⟨CP,hCP,hPCap⟩ := exists_canonicalFirstCoordinateCoefficient_uniform_two_jet_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hL g2 hg2
  obtain ⟨CQ,hCQ,hQCap⟩ := ActualHigherSZeroCoefficientFactorisation.canonicalZeroCoefficientJetTarget_actual
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hL g2 hg2
  obtain ⟨MW,hMW,hWeights⟩ := exists_coordinateWeightBase_uniform_first_caps g g2 hg hg2 L y0 ρ
  let CS : ℝ := 3*MW*data.M
  let COrd : ℝ := 1+CB*CP+CS*CD+CB*CQ+CS*CJ
  have hCS : 0 ≤ CS := by
    dsimp only [CS]
    exact mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hMW)) data.M_nonneg
  have hCOrd : 0 < COrd := by dsimp only [COrd]; positivity
  let etaOrd := min data.eta0 (min etaF etaD)
  have hEtaOrd : 0 < etaOrd := lt_min data.eta0_pos (lt_min hEtaF hEtaD)
  have hE0 : etaOrd ≤ data.eta0 := min_le_left _ _
  have hEF : etaOrd ≤ etaF := (min_le_right _ _).trans (min_le_left _ _)
  have hED : etaOrd ≤ etaD := (min_le_right _ _).trans (min_le_right _ _)
  have hE1 : etaOrd ≤ 1 := hEF.trans hEtaF1
  refine ⟨δ,Cm,hJac,COrd,hCOrd,etaOrd,hEtaOrd,hE0,hE1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaOrd K _hK hBall hb hs hH8
  have heta1 : eta ≤ 1 := hetaOrd.trans hE1
  have hClosed (x : R3) (hx : x ∈ K) : x ∈ closedBall y0 ρ := ball_subset_closedBall (hBall hx)
  have hFormation (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom δ := by
    have hgF := hGuardF q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaOrd.trans hEF)
      x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hgF).self_of_nhds
  have hDataRoom (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom data.δ := by
    have hgD := hGuardD q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaOrd.trans hED)
      x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hgD).self_of_nhds
  refine ⟨hFormation,?_⟩
  intro U V hSU hSV i j x hx
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb1 : 1 ≤ beta := hb x hx
  have hbpos : 0 < beta := zero_lt_one.trans_le hb1
  have hsmall : r*beta^2 ≤ eta := hs x hx
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb1 (n := 2))).trans hsmall).trans heta1
  have hbSq : beta ≤ beta^2 := by nlinarith
  have hrb : r*beta ≤ 1 :=
    ((mul_le_mul_of_nonneg_left hbSq hr.le).trans hsmall).trans heta1
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hr2b : r^2*beta ≤ 1 := by
    have hh := mul_le_mul hr1 hrb (mul_nonneg hr.le hbpos.le) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hh]
  have hTx := hFormation x hx
  have hTV : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hFormation y (hSV hy)
  have hBN0 := (hBCap q hq dr hdr hdr1 Ar hAr p hp eta heta heta1
    x (hClosed x hx) hb1 (hH8 x hx) hsmall i U).2
  have hBScale : CB*eta/beta ≤ CB*eta := div_le_self (by positivity) hb1
  have hBN : ‖finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x‖ ≤ CB*eta*(WHi U x) := by
    have hLiftN : ‖finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)) x‖ =
        ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (1/2 : ℝ))
          (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr U)).val x‖ := by
      rw [norm_finiteCoreSobolevLift]
      simp only [map_neg,Submodule.coe_neg,Pi.neg_apply,norm_neg]
    rw [hLiftN]
    exact hBN0.trans (mul_le_mul_of_nonneg_right hBScale (norm_nonneg _))
  have hPDerivative : ‖directionalFDeriv (coordinateDirection i)
      (fun y => (PL g2 dr Ar p q) y j) x‖ ≤ CP := by
    have hf : ‖fderiv ℝ (fun y => (PL g2 dr Ar p q) y j) x‖ ≤ CP*r^2*beta := by
      simpa only [norm_iteratedFDeriv_one,pow_one,r,beta] using
        hPCap dr Ar p hdr hdr1 hAr hp q hq x hTx hb1 (hsmall.trans heta1) j 1 (by norm_num)
    exact (norm_coordinate_derivative_le _ x i).trans
      (hf.trans (by nlinarith [mul_le_mul_of_nonneg_left hr2b hCP.le]))
  have hQDerivative : ‖directionalFDeriv (coordinateDirection i) ((QL g2 dr Ar p q)) x‖ ≤ CQ := by
    have hf : ‖fderiv ℝ ((QL g2 dr Ar p q)) x‖ ≤ CQ*r*beta := by
      simpa only [norm_iteratedFDeriv_one,pow_one,r,beta] using
        hQCap dr Ar p hdr hdr1 hAr hp q hq x hTx hb1 (hsmall.trans heta1) 1 (by norm_num)
    exact (norm_coordinate_derivative_le _ x i).trans
      (hf.trans (by nlinarith [mul_le_mul_of_nonneg_left hrb hCQ.le]))
  have hDDerivative : ‖directionalFDeriv (coordinateDirection i)
      (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x‖ ≤ CD*eta := by
    have hh := hDCap q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x (hClosed x hx)
      hb1 (hH8 x hx) hsmall j [i] (by simp)
    have hh' : ‖directionalFDeriv (coordinateDirection i)
        (lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p j) x‖ ≤ CD*r*beta^2 := by
      simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial,
        List.length_cons,List.length_nil,Nat.reduceAdd,r,beta,mul_assoc] using hh
    exact hh'.trans (by nlinarith [mul_le_mul_of_nonneg_left hsmall hCD.le])
  have hJD := hJCap q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x (hClosed x hx)
    hb1 (hH8 x hx) hsmall i
  have hWeightsHere (a : Fin 3) : |firstCoordinateWeight g g2 L i a ((Tq dr Ar p q) x)| ≤ MW := by
    rw [firstCoordinateWeight_eq_base]
    exact (hWeights q hq x (hClosed x hx) i a).1
  have hReverse (a : Fin 3) : ‖eH a ((Tq dr Ar p q) x)‖ ≤ data.M := by
    have he := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta
      (hetaOrd.trans hE0) x (hClosed x hx) (hBall hx) hb1 hsmall a a
    exact he.2.2.2.2.1.2.1
  have hPS : ‖actualFirstAdjointHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q i x‖ ≤ CS := by
    have hh := norm_actualFirstAdjointHigh_le
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 dr Ar p q i x MW hWeightsHere hReverse
    have hSmall : CS*r^2 ≤ CS := (mul_le_mul_of_nonneg_left hr2 hCS).trans_eq (mul_one CS)
    exact hh.trans hSmall
  have hBound := nativeOrdinaryProducts_bound_of_actual_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq i j U V hTV x hTx (hDataRoom x hx)
    CB CP CS CD CQ CJ eta hCB.le hCP.le hCS hCD.le hCQ.le hCJ.le heta hb1
    hBN hPS hPDerivative hDDerivative hQDerivative hJD
  exact hBound

/-- Actual first-output smoothness on its original supported formation room. -/
theorem nativeFirstOut_contDiff_of_common_room (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ ((Pout g2 dr Ar p q) j F) := by
  let v : R3 → Half := fun x =>
    (PH g2 dr Ar p q) x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
  have hv : ContDiff ℝ ∞ v := firstHalf_smooth
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data δ Cm g2 hg2 dr Ar p hdr hAr q j F hTF
  have hOut : ContDiff ℝ ∞ (fun x => sphereSobolevHalfToSphereL2L hO hD (v x)) :=
    ordinary_contDiff_half_output hO hD v hv
  have hEq : (fun x => sphereSobolevHalfToSphereL2L hO hD (v x)) =
      (Pout g2 dr Ar p q) j F := by
    funext x
    simp only [v,ActualLowerUSFirstOutput.nativeFirstOut]
  exact Eq.mp (congrArg (fun f : R3 → SphereL2 => ContDiff ℝ ∞ f) hEq) hOut

/-- Derivative P output is smooth on the same actual support room. -/
theorem nativeDerivativePOutput_contDiff_of_common_room (δ : ℝ) (Cm : CRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (i j : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (nativeDerivativePOutput
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q i j F) := by
  have hTDF : ∀ x ∈ tsupport ((dd i) F).val, (Tq dr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F) hx)
  exact (contDiff_directionalFDeriv (coordinateDirection i)
    ((Pout g2 dr Ar p q) j F)
    (nativeFirstOut_contDiff_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 hg2 dr Ar p hdr hAr q j F hTF)).sub
    (nativeFirstOut_contDiff_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 hg2 dr Ar p hdr hAr q j ((dd i) F) hTDF)

/-- Derivative Q output is smooth on the same actual support room. -/
theorem nativeDerivativeQOutput_contDiff_of_common_room (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (nativeDerivativeQOutput
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q i F) := by
  have hTDF : ∀ x ∈ tsupport ((dd i) F).val, (Tq dr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x ((finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F) hx)
  exact (contDiff_directionalFDeriv (coordinateDirection i)
    (nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F)
    (nativeZeroOut_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF).1).sub
    (nativeZeroOut_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq ((dd i) F) hTDF).1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSOrdinaryRows
