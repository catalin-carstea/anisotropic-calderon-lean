import Calderon.ActualLowerUSSecondRowCoefficients
import Calderon.ActualLowerUSGainCapExtraction
import Calderon.FixedParameterProfileBudgets

/-!
GPT-6.1 Sol authoring support; before-code expansion is
lower-u-s-nov03-v001/second-row-next-upfront.md. Concrete first physical
caps of the retained low gains used by the T derivative; no cap callback.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualMixedAngularPairedGains FixedParameterProfilePullback FixedParameterProfileBudgets
  ConformalDepth ReferenceWeightedApproximation

local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/- Canonical imported normed instances are used without private overrides. -/

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
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "Gain" => firstAngularGain
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

attribute [local irreducible] firstAngularGain

/-- Original retained joint first caps, selected once for both actual rooms. -/
theorem exists_firstAngularGain_joint_first_caps (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) :
    ∃ M : ℝ, 0 < M ∧
      (∀ a : Fin 3, ∀ V : Generator,
        ContDiffOn ℝ ∞ (fun t => Gain mixed δ gen a t (Sum.inl V)) (ParamRoom δ)) ∧
      (∀ a b : Fin 3,
        ContDiffOn ℝ ∞ (fun t => Gain mixed δ gen a t (Sum.inr b)) (ParamRoom mixed.δ)) ∧
      (∀ a : Fin 3, ∀ V : Generator, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n (fun t => Gain mixed δ gen a t (Sum.inl V)) (ParamRoom δ) t‖ ≤ M) ∧
      (∀ a b : Fin 3, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom mixed.δ,
        ‖iteratedFDerivWithin ℝ n (fun t => Gain mixed δ gen a t (Sum.inr b)) (ParamRoom mixed.δ) t‖ ≤ M) := by
  have hGeneratorCaps : ∃ MG : ℝ, 0 ≤ MG ∧ ∀ V : Generator, ∀ a : Fin 3,
      ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
      ‖iteratedFDerivWithin ℝ n (gen.low V a) (ParamRoom δ) t‖ ≤ MG :=
    exists_generatorLow_joint_first_cap
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data δ gen
  rcases hGeneratorCaps with ⟨MG,hMG,hG⟩
  have hMixedCaps : ∃ MM : ℝ, 0 ≤ MM ∧ ∀ b a : Fin 3,
      ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom mixed.δ,
      ‖iteratedFDerivWithin ℝ n (mixed.Bl b a) (ParamRoom mixed.δ) t‖ ≤ MM :=
    exists_mixedLow_joint_first_cap
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed
  rcases hMixedCaps with ⟨MM,hMM,hM⟩
  refine ⟨1+MG+MM,by linarith,?_,?_,?_,?_⟩
  · intro a V
    simpa only [firstAngularGain] using gen.smoothLow V a
  · intro a b
    simpa only [firstAngularGain] using (mixed.smooth b a).2.2
  · intro a V n hn t ht
    have hh : ‖iteratedFDerivWithin ℝ n (gen.low V a) (ParamRoom δ) t‖ ≤ 1+MG+MM :=
      (hG V a n hn t ht).trans (by linarith)
    simpa only [firstAngularGain] using hh
  · intro a b n hn t ht
    have hh : ‖iteratedFDerivWithin ℝ n (mixed.Bl b a) (ParamRoom mixed.δ) t‖ ≤ 1+MG+MM :=
      (hM b a n hn t ht).trans (by linarith)
    simpa only [firstAngularGain] using hh

section PhysicalFirstCaps

/- Cache only the already selected canonical low-map normed structures,
AFTER the unchanged qualified-prefix theorem. No parameter-space override. -/
@[instance_reducible] private def physicalGainLowMapNormed :
    NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] physicalGainLowMapNormed
@[instance_reducible] private def physicalGainLowMapSpace :
    NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] physicalGainLowMapSpace

/-- Actual low-map smoothness, value and first derivative caps under the
original profile assumptions. The gain families, room data, profile and all
constants are concrete; no external derivative-cap callback remains. -/
def FirstAngularGainUniformPhysicalFirstCaps
    (mixed : MRoom) (δ : ℝ) (hδ : 0 < δ) (gen : GRoom δ) (hL : 0 < L) : Prop :=
    ∃ M : ℝ, 0 < M ∧ ∃ KT : ℝ, 0 < KT ∧ ∃ etaG : ℝ,
      0 < etaG ∧ etaG ≤ data.eta0 ∧ etaG ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ a : Fin 3, ∀ v : FirstAngularIndex,
      ContDiffAt ℝ ∞ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x ∧
      ‖Gain mixed δ gen a ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x‖ ≤ M*KT

theorem exists_firstAngularGain_uniform_physical_first_caps
    (mixed : MRoom) (δ : ℝ) (hδ : 0 < δ) (gen : GRoom δ) (hL : 0 < L) :
    FirstAngularGainUniformPhysicalFirstCaps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ hδ gen hL := by
  obtain ⟨M,hM,hSmG,hSmM,hCapG,hCapM⟩ := exists_firstAngularGain_joint_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen
  obtain ⟨KT,hKT,hTCap⟩ := exists_uniform_higherSParam_derivative_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨eta0,hEta0,hEta01,hGuardG⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ δ hδ (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨eta1,hEta1,hEta11,hGuardM⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ mixed.δ mixed.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaG := min data.eta0 (min eta0 eta1)
  have hEtaG : 0 < etaG := lt_min data.eta0_pos (lt_min hEta0 hEta1)
  have hEtaG0 : etaG ≤ eta0 := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaG1 : etaG ≤ eta1 := (min_le_right _ _).trans (min_le_right _ _)
  have hUG : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hUM : UniqueDiffOn ℝ (ParamRoom mixed.δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 mixed.δ_pos).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  refine ⟨M,hM,KT,hKT,etaG,hEtaG,min_le_left _ _,hEtaG0.trans hEta01,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs a v
  have heta01 : eta ≤ 1 := hetaG.trans (hEtaG0.trans hEta01)
  have hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hTC := hTCap q hq dr hdr hdr1 Ar hAr p hp eta heta heta01 x hx hb hs
  cases v with
  | inl V =>
    have hmem := higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x
      (hGuardG q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hEtaG0) x hx hxBall hb hs)
    have ht := hmem.self_of_nhds
    have hh := physical_pullback_first_caps
      (fun t => Gain mixed δ gen a t (Sum.inl V)) (Tq dr Ar p q) (ParamRoom δ) x
      (hSmG a V _ ht) hT hmem (hUG _ ht) M
      (hCapG a V 0 (by norm_num) _ ht) (hCapG a V 1 (by norm_num) _ ht)
    exact ⟨hh.1,hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_left hTC hM.le)⟩
  | inr b =>
    have hmem := higherSParam_eventually_mem y0 ρ mixed.δ L dr Ar q p hdr hAr x
      (hGuardM q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hEtaG1) x hx hxBall hb hs)
    have ht := hmem.self_of_nhds
    have hh := physical_pullback_first_caps
      (fun t => Gain mixed δ gen a t (Sum.inr b)) (Tq dr Ar p q) (ParamRoom mixed.δ) x
      (hSmM a b _ ht) hT hmem (hUM _ ht) M
      (hCapM a b 0 (by norm_num) _ ht) (hCapM a b 1 (by norm_num) _ ht)
    exact ⟨hh.1,hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_left hTC hM.le)⟩

end PhysicalFirstCaps

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
