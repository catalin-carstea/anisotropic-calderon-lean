import Calderon.ActualTSPrincipalOrdinaryRoom
import Calderon.ActualTSPrincipalWeightedCoefficients
import Calderon.ActualMixedAngularFullOutputForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalAngularCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly PrincipalCommutator ReferenceDensityBounds
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def mixedNegDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedNegDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def mixedLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] mixedNegDualNormed mixedNegDualSpace mixedLowNormed mixedLowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => ActualFullEGainedEndpoints.CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

open ActualMixedAngularPairedGains ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Omega" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

open ActualTSPrincipalCoefficients ActualTSPrincipalGreen FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain SmoothMetricFrame MovingFrameConnection

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringHigh loweringLow raisingHigh raisingLow loweringEHigh raisingReverseHigh


open ActualTSPrincipalPhysicalGreen
local notation "PK" => angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PT" => angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

/-- Original ordinary E/e germs give the two literal principal angular coefficient germs. -/
lemma principal_joint_regular
    (ordinary : PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom ordinary.δ) :
    ContDiffAt ℝ ∞ (PK i j) t ∧ ContDiffAt ℝ ∞ (PT i j) t := by
  have hs := ordinary.regular j t ht
  unfold angularPrincipalHigh angularPrincipalTransposeHigh
  constructor
  · exact (contDiffAt_const.clm_comp hs.1).sub (contDiffAt_const.clm_comp hs.2.2.1)
  · exact (hs.2.2.2.clm_comp contDiffAt_const).sub (hs.2.1.clm_comp contDiffAt_const)

attribute [local irreducible] angularPrincipalHigh angularPrincipalTransposeHigh

private lemma finite_pair_first_caps {Idx X V : Type} [Fintype Idx]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set X) (hK : IsCompact K) (hU : UniqueDiffOn ℝ K)
    (f ft : Idx → X → V) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) K)
    (hft : ∀ i, ContDiffOn ℝ ∞ (ft i) K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ K,
      ‖iteratedFDerivWithin ℝ n (f i) K t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (ft i) K t‖ ≤ M := by
  classical
  choose Cf hCf using fun i : Idx => exists_compact_iteratedFDerivWithin_bound (f i) K hK hU (hf i) 1
  choose Ct hCt using fun i : Idx => exists_compact_iteratedFDerivWithin_bound (ft i) K hK hU (hft i) 1
  let M : ℝ := ∑ i : Idx, (Cf i+Ct i)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => add_nonneg (hCf i).1 (hCt i).1)
  refine ⟨M,hM,?_⟩
  intro i n hn t ht
  have hi : Cf i+Ct i ≤ M := Finset.single_le_sum
    (fun j _ => add_nonneg (hCf j).1 (hCt j).1) (Finset.mem_univ i)
  have hf0 := (hCf i).1
  have ht0 := (hCt i).1
  exact ⟨((hCf i).2 n hn t ht).trans (by linarith),
    ((hCt i).2 n hn t ht).trans (by linarith)⟩

private lemma physical_first_caps {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Tpar → V) (δ M KT : ℝ) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ ∞ f (ParamRoom δ)) (hU : UniqueDiffOn ℝ (ParamRoom δ))
    (hcap : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
      ‖iteratedFDerivWithin ℝ n f (ParamRoom δ) t‖ ≤ M)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (hTc : ‖fderiv ℝ (Tq dr Ar p q) x‖ ≤ KT) :
    physicalEndpointFirstCaps (L := L) f dr Ar p q x M KT := by
  have hx := hmem.self_of_nhds
  have hc := physical_pullback_first_caps f (Tq dr Ar p q) (ParamRoom δ) x
    (hf _ hx) hT hmem (hU _ hx) M (hcap 0 (by omega) _ hx) (hcap 1 (by omega) _ hx)
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_left hTc hM)⟩

/-- A single actual compact-room cap and strict profile guard for K and its genuine transpose. -/
structure PrincipalAngularPhysicalRoom where
  ordinary : PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
  M : ℝ
  M_nonneg : 0 ≤ M
  KT : ℝ
  KT_pos : 0 < KT
  eta0 : ℝ
  eta0_pos : 0 < eta0
  eta0_le : eta0 ≤ 1
  smooth : ∀ i j : Fin 3,
    ContDiffOn ℝ ∞ (PK i j) (ParamRoom ordinary.δ) ∧
    ContDiffOn ℝ ∞ (PT i j) (ParamRoom ordinary.δ)
  joint_caps : ∀ i j : Fin 3, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom ordinary.δ,
    ‖iteratedFDerivWithin ℝ n (PK i j) (ParamRoom ordinary.δ) t‖ ≤ M ∧
    ‖iteratedFDerivWithin ℝ n (PT i j) (ParamRoom ordinary.δ) t‖ ≤ M
  physical_caps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    (∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom ordinary.δ) ∧
    ∀ i j : Fin 3,
      physicalEndpointFirstCaps (L := L) (PK i j) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (PT i j) dr Ar p q x M KT

/-- All principal angular cap, smoothness and neighborhood premises come from the original native data. -/
theorem exists_principalAngularPhysicalRoom (hL : 0 < L) (hreg : FixedDirichletRegularity) :
    Nonempty (PrincipalAngularPhysicalRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg) := by
  classical
  let ordinary := Classical.choice (exists_principalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg)
  have hK : IsCompact (ParamRoom ordinary.δ) :=
    (isCompact_commonRoom y0 ρ ordinary.δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom ordinary.δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 ordinary.δ_pos).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hSm (i j : Fin 3) : ContDiffOn ℝ ∞ (PK i j) (ParamRoom ordinary.δ) ∧
      ContDiffOn ℝ ∞ (PT i j) (ParamRoom ordinary.δ) := by
    constructor
    · intro t ht
      exact (principal_joint_regular hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg ordinary i j t ht).1.contDiffWithinAt
    · intro t ht
      exact (principal_joint_regular hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg ordinary i j t ht).2.contDiffWithinAt
  let capWitness := finite_pair_first_caps (Idx := Fin 3 × Fin 3) (ParamRoom ordinary.δ) hK hU
    (fun ij => PK ij.1 ij.2) (fun ij => PT ij.1 ij.2)
    (fun ij => (hSm ij.1 ij.2).1) (fun ij => (hSm ij.1 ij.2).2)
  let M : ℝ := Classical.choose capWitness
  have capFacts := Classical.choose_spec capWitness
  let derivWitness := exists_uniform_higherSParam_derivative_bound g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let KT : ℝ := Classical.choose derivWitness
  have derivFacts := Classical.choose_spec derivWitness
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ ordinary.δ ordinary.δ_pos
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let eta0 : ℝ := Classical.choose guardWitness
  have guardFacts := Classical.choose_spec guardWitness
  refine ⟨{
    ordinary := ordinary
    M := M
    M_nonneg := capFacts.1
    KT := KT
    KT_pos := derivFacts.1
    eta0 := eta0
    eta0_pos := guardFacts.1
    eta0_le := guardFacts.2.1
    smooth := hSm
    joint_caps := fun i j n hn t ht => capFacts.2 (i,j) n hn t ht
    physical_caps := ?_
  }⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs
  have hGuard := guardFacts.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ ordinary.δ L dr Ar q p hdr hAr x hGuard
  have hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hTc := derivFacts.2 q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0le.trans guardFacts.2.1) x hx hb hs
  refine ⟨hmem,?_⟩
  intro i j
  constructor
  · exact physical_first_caps (L := L) (y0 := y0) (ρ := ρ) _ ordinary.δ M KT capFacts.1
      (hSm i j).1 hU (fun n hn t ht => (capFacts.2 (i,j) n hn t ht).1)
      dr Ar p q x hT hmem hTc
  · exact physical_first_caps (L := L) (y0 := y0) (ρ := ρ) _ ordinary.δ M KT capFacts.1
      (hSm i j).2 hU (fun n hn t ht => (capFacts.2 (i,j) n hn t ht).2)
      dr Ar p q x hT hmem hTc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalAngularCaps
