import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualHigherSAllAtomNativeFirstCaps
import Calderon.FixedParameterProfileBudgets
import Calderon.FixedParameterProfilePullback

/-! Same-W all16 actual within-profile first caps. Original pullback
budgets and strict guards discharge all domain/regularity premises; constants
precede every profile/input. Standard native derivative norms are selected explicitly. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAllAtomProfileCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualRetainedGeneratorMultiplierGains
  ReferenceWeightedApproximation FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

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
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L


lemma exists_finite_profile_family_first_caps {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (y0 : R3) (rho d : ℝ) (hrho : 0 < rho) (hd : 0 < d)
    (f : ι → Tpar → V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i)
      (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)))
    (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ i, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ Set.prod (commonRoom y0 rho d)
      (closedBall (0 : R3 →L[ℝ] ℝ) 1), ‖iteratedFDerivWithin ℝ n (f i)
        (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) t‖ ≤ M) :
    ∃ KT : ℝ, 0 < KT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eps →
      StrictPhysicalProfileGuard y0 rho d q (referenceRadius dr Ar p L) x →
      ∀ i, ContDiffAt ℝ ∞ (fun y => f i (ActualHigherSFormation.higherSParam L dr Ar p q y)) x ∧
        ‖f i (ActualHigherSFormation.higherSParam L dr Ar p q x)‖ ≤ M ∧
        ‖fderiv ℝ (fun y => f i (ActualHigherSFormation.higherSParam L dr Ar p q y)) x‖ ≤ M*KT := by
  classical
  choose KTi hKTi using fun i => FixedParameterProfileBudgets.exists_higherSParam_family_first_caps
    g hg L hL y0 rho d hrho hd (closedBall y0 rho) (isCompact_closedBall _ _) (f i) (hf i) M hM (hcap i)
  let KT := 1+∑ i : ι, KTi i
  have hsum : 0 ≤ ∑ i : ι, KTi i := Finset.sum_nonneg (fun i _ => (hKTi i).1.le)
  refine ⟨KT, by dsimp [KT]; linarith, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eps he he1 x hx hb hs hguard i
  have h := (hKTi i).2 q hq dr hdr hdr1 Ar hAr p hp eps he he1 x hx hb hs hguard
  have hOne : KTi i ≤ KT := (Finset.single_le_sum (fun j _ => (hKTi j).1.le) (Finset.mem_univ i)).trans
    (by dsimp [KT]; linarith)
  exact ⟨h.1, h.2.1, h.2.2.trans (mul_le_mul_of_nonneg_left hOne hM)⟩

-- These are explicit applications of the existing standard Mathlib norm only.
-- No norm instance is declared or replaced.
local notation "DHNorm" => @Norm.norm (R3 →L[ℝ] (Hi →L[ℝ] Half))
  (ContinuousLinearMap.hasOpNorm (E := R3) (F := Hi →L[ℝ] Half) (σ₁₂ := RingHom.id ℝ))
local notation "DLNorm" => @Norm.norm (R3 →L[ℝ] (Half →L[ℝ] Neg))
  (ContinuousLinearMap.hasOpNorm (E := R3) (F := Half →L[ℝ] Neg) (σ₁₂ := RingHom.id ℝ))

structure ActualAtomProfileFirstCapsAt (C dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Prop where
  highSmooth : ∀ aa : ZeroAtom, ContDiffAt ℝ ∞ (fun y => AH ((Tq dr Ar p q) y) aa) x
  lowSmooth : ∀ aa : ZeroAtom, ContDiffAt ℝ ∞ (fun y => AL ((Tq dr Ar p q) y) aa) x
  reverseHighSmooth : ∀ aa : ZeroAtom, ContDiffAt ℝ ∞ (fun y => RH ((Tq dr Ar p q) y) aa) x
  reverseLowSmooth : ∀ aa : ZeroAtom, ContDiffAt ℝ ∞ (fun y => RL ((Tq dr Ar p q) y) aa) x
  highBound : ∀ aa : ZeroAtom, ‖AH ((Tq dr Ar p q) x) aa‖ ≤ C
  lowBound : ∀ aa : ZeroAtom, ‖AL ((Tq dr Ar p q) x) aa‖ ≤ C
  reverseHighBound : ∀ aa : ZeroAtom, ‖RH ((Tq dr Ar p q) x) aa‖ ≤ C
  reverseLowBound : ∀ aa : ZeroAtom, ‖RL ((Tq dr Ar p q) x) aa‖ ≤ C
  highDerivativeBound : ∀ aa : ZeroAtom, DHNorm (fderiv ℝ (fun y => AH ((Tq dr Ar p q) y) aa) x) ≤ C
  lowDerivativeBound : ∀ aa : ZeroAtom, DLNorm (fderiv ℝ (fun y => AL ((Tq dr Ar p q) y) aa) x) ≤ C
  reverseHighDerivativeBound : ∀ aa : ZeroAtom, DHNorm (fderiv ℝ (fun y => RH ((Tq dr Ar p q) y) aa) x) ≤ C
  reverseLowDerivativeBound : ∀ aa : ZeroAtom, DLNorm (fderiv ℝ (fun y => RL ((Tq dr Ar p q) y) aa) x) ≤ C
local notation "ProfileCaps" => ActualAtomProfileFirstCapsAt
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow sphereSobolevInclusionL

theorem exists_actual_allAtom_profile_first_caps {d : ℝ} (hd : 0 < d)
    (P : ARoom d) (hL : 0 < L) :
    ∃ Cprof etaProf : ℝ, 1 ≤ Cprof ∧ 0 < etaProf ∧ etaProf ≤ data.eta0 ∧ etaProf ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaProf →
      ∀ K : Set R3, K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ K, ProfileCaps Cprof dr Ar p q x := by
  obtain ⟨M, hM, hNative⟩ := ActualHigherSAllAtomNativeCaps.exists_actual_allAtom_native_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  obtain ⟨KA, hKA, hA⟩ := exists_finite_profile_family_first_caps g hg L hL y0 ρ d hData.1.2.1 hd
    (fun aa t => AH t aa) hNative.highSmooth M hM0 hNative.highJetBound
  obtain ⟨KLw, hKLw, hLow⟩ := exists_finite_profile_family_first_caps g hg L hL y0 ρ d hData.1.2.1 hd
    (fun aa t => AL t aa) hNative.lowSmooth M hM0 hNative.lowJetBound
  obtain ⟨KB, hKB, hB⟩ := exists_finite_profile_family_first_caps g hg L hL y0 ρ d hData.1.2.1 hd
    (fun aa t => RH t aa) hNative.reverseHighSmooth M hM0 hNative.reverseHighJetBound
  obtain ⟨KR, hKR, hRevLow⟩ := exists_finite_profile_family_first_caps g hg L hL y0 ρ d hData.1.2.1 hd
    (fun aa t => RL t aa) hNative.reverseLowSmooth M hM0 hNative.reverseLowJetBound
  obtain ⟨epsG, hepsG, _hepsG1, hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Cprof := 1+M+M*(KA+KLw+KB+KR)
  let etaProf := min data.eta0 (min 1 epsG)
  have hMKA : 0 ≤ M*KA := mul_nonneg hM0 hKA.le
  have hMKL : 0 ≤ M*KLw := mul_nonneg hM0 hKLw.le
  have hMKB : 0 ≤ M*KB := mul_nonneg hM0 hKB.le
  have hMKR : 0 ≤ M*KR := mul_nonneg hM0 hKR.le
  have hMC : M ≤ Cprof := by dsimp [Cprof]; nlinarith
  have hMAC : M*KA ≤ Cprof := by dsimp [Cprof]; nlinarith
  have hMLC : M*KLw ≤ Cprof := by dsimp [Cprof]; nlinarith
  have hMBC : M*KB ≤ Cprof := by dsimp [Cprof]; nlinarith
  have hMRC : M*KR ≤ Cprof := by dsimp [Cprof]; nlinarith
  refine ⟨Cprof, etaProf, by dsimp [Cprof]; nlinarith,
    lt_min data.eta0_pos (lt_min zero_lt_one hepsG), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaProf K hK hb hs x hx
  have heta1 : eta ≤ 1 := hetaProf.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaG : eta ≤ epsG := hetaProf.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxClosed := ball_subset_closedBall (hK hx)
  have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hxClosed (hK hx) (hb x hx) (hs x hx)
  have hA' (aa : ZeroAtom) := hA q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed (hb x hx) (hs x hx) hguard aa
  have hL' (aa : ZeroAtom) := hLow q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed (hb x hx) (hs x hx) hguard aa
  have hB' (aa : ZeroAtom) := hB q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed (hb x hx) (hs x hx) hguard aa
  have hR' (aa : ZeroAtom) := hRevLow q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed (hb x hx) (hs x hx) hguard aa
  exact {
    highSmooth := fun aa => (hA' aa).1
    lowSmooth := fun aa => (hL' aa).1
    reverseHighSmooth := fun aa => (hB' aa).1
    reverseLowSmooth := fun aa => (hR' aa).1
    highBound := fun aa => ((hA' aa).2.1).trans hMC
    lowBound := fun aa => ((hL' aa).2.1).trans hMC
    reverseHighBound := fun aa => ((hB' aa).2.1).trans hMC
    reverseLowBound := fun aa => ((hR' aa).2.1).trans hMC
    highDerivativeBound := fun aa => ((hA' aa).2.2).trans hMAC
    lowDerivativeBound := fun aa => ((hL' aa).2.2).trans hMLC
    reverseHighDerivativeBound := fun aa => ((hB' aa).2.2).trans hMBC
    reverseLowDerivativeBound := fun aa => ((hR' aa).2.2).trans hMRC }

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAllAtomProfileCaps
