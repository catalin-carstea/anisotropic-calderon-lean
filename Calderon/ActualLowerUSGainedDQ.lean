import Calderon.ActualLowerUSDQDensity
import Calderon.ActualLowerUSDPresentations
import Calderon.ActualLowerUSGeneratorZeroCommutator
import Calderon.ActualLowerUSZeroAngularSum
import Calderon.ActualLowerUSAdjointPresentation
import Calderon.ActualLowerUSFirstAdjointNorm
import Calderon.ActualLowerUSFirstCoefficientJets
import Calderon.ActualLowerUSIndexedAngularGraphs
import Calderon.ActualLowerUSAdjointCore

/-!
Author: GPT-6.1 Sol, author support only.
Before-code: ../lower-r-z-dq-contraction-upfront.md.
Exact native D/Q contraction, including scalar cancellation before its angular
mass estimate. No physical Q output is asserted finite. No author compilation.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSZeroAngularSum ActualLowerUSGeneratorZeroCommutator
  ActualLowerUSFiniteQuadraticCommutator ActualHigherSZeroPhysicalGraph
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints



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

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q




local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Qout" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "Comp" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  lowerGeneratorZeroCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
private abbrev finiteWeightValue (s : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "WH" F:max x:max => ‖finiteWeightValue hO hD (1/2 : ℝ) F x‖
local notation "WHi" F:max x:max => ‖finiteWeightValue hO hD (3/2 : ℝ) F x‖

/-- Exact contraction into the primitive density. Identity/scalar terms cancel
here, before any absolute-value or coefficient-mass estimate. -/
private theorem nativeDZeroCommutatorDensity_eq_angular_sum
    (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (j : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD)
    (hTV : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δ) (x : R3) :
    nativeDZeroCommutatorDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q j U V x =
      ∑ v : FirstAngularIndex, firstAngularCoefficient g L g2 q dr Ar p j x v *
        (Comp g2 dr Ar p hdr hAr q) (Sum.inr v) U V x := by
  let DD := nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j
  let GG := lowerCoreAngularGenerator hO hD hF
  let GS := lowerCoreAngularGeneratorAdjoint hO hD hF
  let c := nativeDFirstCoefficient g g2 L q dr Ar p j
  let hc := contDiff_nativeDFirstCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j
  have hDPres := nativeD_eq_first_presentation hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j
  have hDs := nativeDstar_eq_first_presentation hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j
  have hTD : ∀ y ∈ tsupport (DD V).val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hTV y ((finiteCoreSupportPreserving_nativeULowerAdjointFirstCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j V) hy)
  have hTG : ∀ i : LowerCoreAngularGeneratorIndex, ∀ y ∈ tsupport (GG i V).val,
      (Tq dr Ar p q) y ∈ ParamRoom δ := by
    intro i y hy
    have hSupp := finiteCoreSupportPreserving_of_pointwise_adjoint hO hD (GG i) (GS i)
      (fun F G z => (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF i z).2.1 F G)
    exact hTV y (hSupp V hy)
  have hLift : finiteCoreSobolevLift hO hD (3/2 : ℝ) (DD V) x =
      ∑ i : LowerCoreAngularGeneratorIndex, c i x • finiteCoreSobolevLift hO hD (3/2 : ℝ) (GG i V) x := by
    have hRaw := congrArg
      (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
        finiteCoreSobolevLift hO hD (3/2 : ℝ) (A V) x) hDPres
    have hPresent := finiteCoreSobolevLift_presentation hO hD (3/2 : ℝ) GG c hc V x
    exact hRaw.trans hPresent
  have hQ := nativeZeroOut_weighted_sum_of_lift_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq
    (fun i => c i x) (DD V) (fun i => GG i V) hTD hTG x hLift
  have hStar : -(nativeB hO hD hF g g2 hg L q dr Ar p j hg2 hdr hAr U).val x =
      ∑ i : LowerCoreAngularGeneratorIndex, c i x • (GS i U).val x := by
    have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => (T U).val x) hDs
    simpa only [coreScalarCombination,LinearMap.neg_apply,LinearMap.sum_apply,
      Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
      Submodule.coe_mk,Submodule.coe_neg,Pi.neg_apply,Submodule.coe_sum,Finset.sum_apply] using he
  unfold nativeDZeroCommutatorDensity
  rw [hStar,hQ]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    ← Finset.sum_sub_distrib,← mul_sub]
  simp only [c,GG,GS,LowerCoreAngularGeneratorIndex,Fintype.sum_sum_type,Fintype.sum_unique,
    nativeDFirstCoefficient,lowerGeneratorZeroCommutatorDensity,lowerCoreAngularGenerator,
    lowerCoreAngularGeneratorAdjoint,Module.End.one_apply,sub_self,mul_zero,zero_add]


/-- Complete native gained D/Q producer; original scalar cancels exactly. -/
theorem exists_nativeDZeroCommutator_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, ∃ Cm : CRoom δ,
      (∀ z ∈ commonRoom y0 ρ δ,
        ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∃ C_DQ : ℝ, 0 < C_DQ ∧ ∃ etaDQ : ℝ, 0 < etaDQ ∧
      etaDQ ≤ data.eta0 ∧ etaDQ ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaDQ →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x *
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤
          eta*referenceRadius dr Ar p L x) →
      (∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom δ) ∧
      ∀ j : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      tsupport U.val ⊆ K → tsupport V.val ⊆ K → ∀ x ∈ K,
        |nativeDZeroCommutatorDensity
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          g2 hg2 dr Ar p hdr hAr q j U V x| ≤
          (C_DQ*eta/actualReferenceBeta g L q dr Ar p x)*(WH U x)*(WHi V x) ∧
        |nativeDZeroCommutatorDensity
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          g2 hg2 dr Ar p hdr hAr q j U V x| ≤
          (C_DQ*eta/actualReferenceBeta g L q dr Ar p x)*(WHi U x)*(WH V x) := by
  obtain ⟨δ,Cm,hJac,CG,hCG,etaG,hEtaG,hEtaG0,hEtaG1,hPrimitive⟩ :=
    exists_lowerGeneratorZeroCommutator_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CB,hCB,hMass⟩ := exists_nativeBAngularPartMass_uniform_smallness
    hO hD g g2 hg hg2 L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨δ,Cm,hJac,CG*CB,mul_pos hCG hCB,etaG,hEtaG,hEtaG0,hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hBall hb hs hH8
  have hP := hPrimitive q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hBall hb hs hH8
  refine ⟨hP.1,?_⟩
  intro j U V hSU hSV x hx
  have hxClosed : x ∈ closedBall y0 ρ := ball_subset_closedBall (hBall hx)
  have heta1 : eta ≤ 1 := hetaG.trans hEtaG1
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hbpos : 0 < beta := zero_lt_one.trans_le (hb x hx)
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ (hb x hx) (n := 2))).trans (hs x hx)).trans heta1
  have hSum := nativeDZeroCommutatorDensity_eq_angular_sum
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq j U V
    (fun y hy => hP.1 y (hSV hy)) x
  have hAngularMass : (∑ v : FirstAngularIndex,
      |firstAngularCoefficient g L g2 q dr Ar p j x v|) ≤ CB*eta/beta :=
    (firstAngularCoefficient_mass_le g L g2 q dr Ar p j x).trans
      (hMass q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed
        (hb x hx) (hH8 x hx) (hs x hx) j)
  have hRate : 0 ≤ (CG*CB)*eta/beta := div_nonneg (by positivity) hbpos.le
  have hMassRate : CG*r*(∑ v : FirstAngularIndex,
      |firstAngularCoefficient g L g2 q dr Ar p j x v|) ≤ (CG*CB)*eta/beta := by
    calc
      _ ≤ CG*r*(CB*eta/beta) := mul_le_mul_of_nonneg_left hAngularMass (by positivity)
      _ = ((CG*CB)*eta/beta)*r := by ring
      _ ≤ (CG*CB)*eta/beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 hRate
  have hBound (theta : ℝ) (htheta : 0 ≤ theta)
      (hComp : ∀ v : FirstAngularIndex,
        |(Comp g2 dr Ar p hdr hAr q) (Sum.inr v) U V x| ≤ CG*r*theta) :
      |nativeDZeroCommutatorDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q j U V x| ≤ ((CG*CB)*eta/beta)*theta := by
    calc
      _ = |∑ v : FirstAngularIndex, firstAngularCoefficient g L g2 q dr Ar p j x v *
          (Comp g2 dr Ar p hdr hAr q) (Sum.inr v) U V x| := congrArg abs hSum
      _ ≤ ∑ v : FirstAngularIndex,
          |firstAngularCoefficient g L g2 q dr Ar p j x v *
            (Comp g2 dr Ar p hdr hAr q) (Sum.inr v) U V x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : FirstAngularIndex,
          |firstAngularCoefficient g L g2 q dr Ar p j x v| * (CG*r*theta) := by
        apply Finset.sum_le_sum
        intro v _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hComp v) (abs_nonneg _)
      _ = (CG*r*(∑ v : FirstAngularIndex,
          |firstAngularCoefficient g L g2 q dr Ar p j x v|))*theta := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ ((CG*CB)*eta/beta)*theta := mul_le_mul_of_nonneg_right hMassRate htheta
  constructor
  · simpa only [mul_assoc] using hBound ((WH U x)*(WHi V x)) (by positivity)
      (fun v => by simpa only [r,mul_assoc] using (hP.2 (Sum.inr v) U V hSU hSV x hx).1)
  · simpa only [mul_assoc] using hBound ((WHi U x)*(WH V x)) (by positivity)
      (fun v => by simpa only [r,mul_assoc] using (hP.2 (Sum.inr v) U V hSU hSV x hx).2)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
