import Calderon.ActualPiMixedWeakEndpointCore
import Calderon.ActualAngularPiDraft
import Calderon.ActualAngularPiRotationCoefficientTopology
import Calderon.ActualAngularPiRawZeroTopologyTransferJointRegularity
import Calderon.ActualAngularRadialRemainderTopology
import Calderon.ActualPiNativeOperatorGerms
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeSmoothMultiplierCommonSupportJets

/-! One theorem: one room `δ = min δA dP` and one set of witnesses `G` (from the angular theorem,
obtained once) and `m, Km` (from the germ theorem, obtained once) carry
* the actual Pi graphs, proved on these witnesses rather than obtained from the
  existential `exists_reference_commonRadius_actualPi_mixed_graphs`,
* joint `ContDiffOn ℝ ∞` of the four exact maps on `S = commonRoom y0 ρ δ ×ˢ closedBall 0 1`,
* for every `N`, one nonnegative cap for all within-jets of order `≤ N`, all `i k`, all four maps.
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation MetricOperator
  NormalCoordinatesFrame NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier NativeNegativeHalfSmoothMultiplier ActualAngularHighDraft

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)

local instance v015PiHighComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v015PiHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v015PiNegativeComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))
local notation "natH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "low" => smoothMultiplierLowerJets

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity) (hg : IsAdmissibleMetric g)
  (hKernel : UnitBallValueTraceKernel τ0)

/-! ### The four exact maps as functions of `z = (p, ℓ)`; `Q` frozen at the CURRENT `z` -/

/-- `z ↦ E[a,Pi]_{ik}(z) = loweringPiGain (Q_k z) i q y` (raw operator at `(q,(y,0))`). -/
def v015LoweringPiGainMap (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (z : Tpar) : Hi →L[ℝ] Hi :=
  loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
    (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) i z.1.1 z.1.2.1

/-- `z ↦ E[Pi,A]_{ik}(z) = raisingPiGain (Q_k z) i q y`. -/
def v015RaisingPiGainMap (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (z : Tpar) : Half →L[ℝ] Half :=
  raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) i z.1.1 z.1.2.1

/-- `z ↦ C[a_i, T Pi_k](z) = loweringMixed G (Q_k z) i p`. -/
def v015LoweringMixedMap (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (z : Tpar) : Hi →L[ℝ] Half :=
  loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg G
    (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) i z.1

/-- `z ↦ C[Pi_k S, A_i](z) = raisingMixed (Q_k z) i p`. -/
def v015RaisingMixedMap (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (z : Tpar) : Hi →L[ℝ] Half :=
  raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
    (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) i z.1

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ShS" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SlS" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CAS" => raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0
  g L y0 Φ B ε C ρ H a w hData hreg
local notation "EaPiMap" => v015LoweringPiGainMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "EPiAMap" => v015RaisingPiGainMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaTPiMap" => v015LoweringMixedMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
  hreg hg
local notation "CPiSAMap" => v015RaisingMixedMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
  hreg
local notation "PiRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

-- Keep the native operator implementations opaque to elaboration.
-- This does not change their mathematical interfaces or definitions.
attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevLinearCoordinateMulL
  rawAdjointMultiplierZero rawHalfMultiplierZero rotationJets commonSupportCoefficientFamily
  adjointHighRemainder adjointHalfRemainder sharpRemainder lowerSharpRemainder
  loweringAngularHighCommutator raisingCommutator

private lemma actualPiMixedCaps_lowering_smooth
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (s : Set Tpar)
    (hRaw : ContDiffOn ℝ ∞ (fun z : Tpar =>
      rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) z.1.1 z.1.2.1) s) :
    ContDiffOn ℝ ∞ (EaPiMap m hm Km hKm hmz i k) s := by
  unfold v015LoweringPiGainMap loweringPiGain
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro j _
    exact contDiffOn_const.clm_comp
      (contDiff_nativeThreeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
        (m k) (hm k) Km hKm (hmz k) j i).contDiffOn
  · exact contDiffOn_const.clm_comp hRaw

private lemma actualPiMixedCaps_raising_smooth
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (s : Set Tpar)
    (hRaw : ContDiffOn ℝ ∞ (fun z : Tpar =>
      rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) z.1.1 z.1.2.1) s) :
    ContDiffOn ℝ ∞ (EPiAMap m hm Km hKm hmz i k) s := by
  unfold v015RaisingPiGainMap raisingPiGain
  apply ContDiffOn.sub
  · apply ContDiffOn.sum
    intro j _
    exact (contDiff_nativeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
      (m k) (hm k) Km hKm (hmz k) j i).contDiffOn.clm_comp contDiffOn_const
  · exact hRaw.clm_comp contDiffOn_const

private lemma actualPiMixedCaps_lowering_mixed_smooth
    (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (s : Set Tpar)
    (hCaT : ContDiffOn ℝ ∞ (fun z : Tpar => CaT G i z.1) s)
    (hTh : ContDiffOn ℝ ∞ (fun z : Tpar => Th z.1) s)
    (hE1 : ContDiffOn ℝ ∞ (EaPiMap m hm Km hKm hmz i k) s) :
    ContDiffOn ℝ ∞ (CaTPiMap G m hm Km hKm hmz i k) s := by
  unfold v015LoweringMixedMap loweringMixed
  apply ContDiffOn.add
  · exact hCaT.clm_comp (contDiff_nativeThreeHalfCoefficientMulL_commonSupport
      hcalc hF hO hD τ0 (m k) (hm k) Km hKm (hmz k)).contDiffOn
  · exact hTh.clm_comp hE1

private lemma actualPiMixedCaps_raising_mixed_smooth
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (i k : Fin 3) (s : Set Tpar)
    (hCAS : ContDiffOn ℝ ∞ (fun z : Tpar => CAS i z.1) s)
    (hSh : ContDiffOn ℝ ∞ (fun z : Tpar => ShS z.1) s)
    (hE2 : ContDiffOn ℝ ∞ (EPiAMap m hm Km hKm hmz i k) s) :
    ContDiffOn ℝ ∞ (CPiSAMap m hm Km hKm hmz i k) s := by
  have hNatL : ContDiff ℝ ∞ (fun z : Tpar =>
      natL (low (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
        (m k) (hm k) Km hKm (hmz k)
  unfold v015RaisingMixedMap raisingMixed
  apply ContDiffOn.add
  · exact (hNatL.contDiffOn.clm_comp hCAS).neg
  · exact hE2.clm_comp hSh

private lemma actualPiMixedCaps_common_cap
    (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0)
    (δ : ℝ) (hSK : IsCompact (PiRoom δ)) (hSU : UniqueDiffOn ℝ (PiRoom δ))
    (hE1On : ∀ i k, ContDiffOn ℝ ∞ (EaPiMap m hm Km hKm hmz i k) (PiRoom δ))
    (hE2On : ∀ i k, ContDiffOn ℝ ∞ (EPiAMap m hm Km hKm hmz i k) (PiRoom δ))
    (hC1On : ∀ i k, ContDiffOn ℝ ∞ (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ))
    (hC2On : ∀ i k, ContDiffOn ℝ ∞ (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ)) : ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i k : Fin 3, ∀ n : ℕ, n ≤ N → ∀ z ∈ PiRoom δ,
      ‖iteratedFDerivWithin ℝ n (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M := by
  intro N
  choose M1 hM1 using fun i k : Fin 3 => v015_exists_iteratedFDerivWithin_cap
    (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) hSK hSU (hE1On i k) N
  choose M2 hM2 using fun i k : Fin 3 => v015_exists_iteratedFDerivWithin_cap
    (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) hSK hSU (hE2On i k) N
  choose M3 hM3 using fun i k : Fin 3 => v015_exists_iteratedFDerivWithin_cap
    (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) hSK hSU (hC1On i k) N
  choose M4 hM4 using fun i k : Fin 3 => v015_exists_iteratedFDerivWithin_cap
    (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ) hSK hSU (hC2On i k) N
  have h0 (i k : Fin 3) : 0 ≤ M1 i k + M2 i k + M3 i k + M4 i k := by
    linarith [(hM1 i k).1, (hM2 i k).1, (hM3 i k).1, (hM4 i k).1]
  have hle (i k : Fin 3) : M1 i k + M2 i k + M3 i k + M4 i k ≤
      ∑ i' : Fin 3, ∑ k' : Fin 3, (M1 i' k' + M2 i' k' + M3 i' k' + M4 i' k') :=
    calc M1 i k + M2 i k + M3 i k + M4 i k
        ≤ ∑ k' : Fin 3, (M1 i k' + M2 i k' + M3 i k' + M4 i k') :=
          Finset.single_le_sum (f := fun k' => M1 i k' + M2 i k' + M3 i k' + M4 i k')
            (fun k' _ => h0 i k') (Finset.mem_univ k)
      _ ≤ ∑ i' : Fin 3, ∑ k' : Fin 3, (M1 i' k' + M2 i' k' + M3 i' k' + M4 i' k') :=
          Finset.single_le_sum
            (f := fun i' => ∑ k' : Fin 3, (M1 i' k' + M2 i' k' + M3 i' k' + M4 i' k'))
            (fun i' _ => Finset.sum_nonneg (fun k' _ => h0 i' k')) (Finset.mem_univ i)
  refine ⟨∑ i' : Fin 3, ∑ k' : Fin 3, (M1 i' k' + M2 i' k' + M3 i' k' + M4 i' k'),
    Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun k' _ => h0 i' k')), ?_⟩
  intro i k n hn z hz
  have h1 := (hM1 i k).2 n hn z hz
  have h2 := (hM2 i k).2 n hn z hz
  have h3 := (hM3 i k).2 n hn z hz
  have h4 := (hM4 i k).2 n hn z hz
  have a1 := (hM1 i k).1
  have a2 := (hM2 i k).1
  have a3 := (hM3 i k).1
  have a4 := (hM4 i k).1
  have hl := hle i k
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Final theorem: graphs + joint smoothness + uniform caps, SAME witnesses -/

include hreg hg hKernel in
theorem exists_reference_commonRadius_actualPi_mixed_graph_caps :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ)) ∧
      (∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ v : Half,
        JL (G j p v) = Tl p ((Ml j) v) - (Mn j) (Tl p v)) ∧
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k)) (Km : Set R3)
      (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0),
      (∀ i k : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ ell ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1,
        let Q := commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (p,ell)
        (natH Q = PiH k (p,ell) ∧ natL (low Q) = PiL k (p,ell) ∧
          natN (low Q) = PiN k (p,ell)) ∧
        (∀ u : Hi,
          IH (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i p.1 p.2.1 u) =
            loweringHigh hF hO hD i (PiH k (p,ell) u) -
              PiL k (p,ell) (loweringHigh hF hO hD i u)) ∧
        (∀ v : Half,
          JL (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i p.1 p.2.1 v) =
            PiN k (p,ell) (raisingLow hF hO hD i v) -
              raisingLow hF hO hD i (PiL k (p,ell) v)) ∧
        (∀ u : Hi,
          JL (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg G Q i p u) =
            loweringLow hF hO hD i (Th p (PiH k (p,ell) u)) -
              Tl p (PiL k (p,ell) (loweringHigh hF hO hD i u))) ∧
        (∀ u : Hi,
          JL (raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Q i p u) =
            PiN k (p,ell) (SlS p (raisingHigh hF hO hD i u)) -
              raisingLow hF hO hD i (PiL k (p,ell) (ShS p u)))) ∧
      (∀ i k : Fin 3,
        ContDiffOn ℝ ∞ (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) ∧
        ContDiffOn ℝ ∞ (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) ∧
        ContDiffOn ℝ ∞ (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) ∧
        ContDiffOn ℝ ∞ (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ)) ∧
      ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i k : Fin 3, ∀ n : ℕ, n ≤ N → ∀ z ∈ PiRoom δ,
        ‖iteratedFDerivWithin ℝ n (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M := by
  have hρ : 0 < ρ := hData.1.2.1
  -- witnesses obtained once
  have hBoth := exists_reference_commonRadius_angularHigh_both_graph_caps
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  obtain ⟨δA,hδA,hδAρ,hRoomA,G,hGOn,hGlow,hCaT,_hGh,hCAS⟩ := hBoth
  have hGuard := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  obtain ⟨lam,Lam,d,_hlam,hd,_hdρ,hFin⟩ := hGuard
  have hGerms := exists_referencePi_commonSupport_native_operator_germs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨dP,hdP,_hdPρ,m,hm,Km,hKm,hmz,hGerm⟩ := hGerms
  -- ONE room, chosen before `N`, `z`, cutoffs and inputs
  let δ : ℝ := min δA dP
  have hδ : 0 < δ := lt_min hδA hdP
  have hSubA : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δA := commonRoom_mono y0 ρ (min_le_left _ _)
  have hSubP : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dP := commonRoom_mono y0 ρ (min_le_right _ _)
  -- (R3) the SAME finite-room guard at the zero radial operator point
  have hG0 (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) : Guard lam Lam (p.1,(p.2.1,0)) :=
    hFin (p.1,(p.2.1,0))
      (show (p.1,(p.2.1,(0 : ℝ))) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) from
        ⟨hp.1,hp.2.1,
          (show (0 : ℝ) ∈ Icc (-d) d from Set.mem_Icc.mpr ⟨by linarith,by linarith⟩)⟩)
  -- (R5),(R6) compact UniqueDiffOn parameter set
  have hSK : IsCompact (PiRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hSU : UniqueDiffOn ℝ (PiRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hρ hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hMapsA : MapsTo (Prod.fst : Tpar → Pphys) (PiRoom δ) (commonRoom y0 ρ δA) :=
    fun z hz => hSubA hz.1
  -- (D),(E) raw zero-radial multipliers, guard at `p⁰`
  have hRawHOn (k : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar =>
      rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) z.1.1 z.1.2.1)
      (PiRoom δ) := fun z hz =>
    (contDiffAt_rawAdjointMultiplierZero_commonSupport hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hg (m k) (hm k) Km hKm (hmz k)
      (fun z : Tpar => z.1.1) contDiff_fst.fst (fun z : Tpar => z.1.2.1) contDiff_fst.snd.fst z
      (by
        unfold referenceGaugeNormalHighInvertibleLocus
        exact (hG0 z.1 hz.1).2.2.2.1)).contDiffWithinAt
  have hRawLOn (k : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar =>
      rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z) z.1.1 z.1.2.1)
      (PiRoom δ) := fun z hz =>
    (contDiffAt_rawHalfMultiplierZero_commonSupport hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData (m k) (hm k) Km hKm (hmz k)
      (fun z : Tpar => z.1.1) contDiff_fst.fst (fun z : Tpar => z.1.2.1) contDiff_fst.snd.fst z
      (hG0 z.1 hz.1).2.2.1.1 (hG0 z.1 hz.1).2.2.1.2.1).contDiffWithinAt
  -- (F) signed radial remainders under the full segment guard (R4)
  have hRem (z : Tpar) (hz : z ∈ PiRoom δ) :=
    contDiffAt_actualAngularRadialRemainder_families_of_segment hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg z.1
      (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoomA
        z.1 (hSubA hz.1))
  have hThOn : ContDiffOn ℝ ∞ (fun z : Tpar => Th z.1) (PiRoom δ) := fun z hz =>
    ((hRem z hz).1.comp (f := fun z : Tpar => z.1) z contDiffAt_fst).contDiffWithinAt
  have hShOn : ContDiffOn ℝ ∞ (fun z : Tpar => ShS z.1) (PiRoom δ) := fun z hz =>
    ((hRem z hz).2.2.1.comp (f := fun z : Tpar => z.1) z contDiffAt_fst).contDiffWithinAt
  -- (G) original angular WITHIN smoothness, by projection and MapsTo
  have hCaTOn (i : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => CaT G i z.1) (PiRoom δ) :=
    (hCaT i).2.1.comp contDiffOn_fst hMapsA
  have hCASOn (i : Fin 3) : ContDiffOn ℝ ∞ (fun z : Tpar => CAS i z.1) (PiRoom δ) :=
    (hCAS i).2.1.comp contDiffOn_fst hMapsA
  have hE1On (i k : Fin 3) : ContDiffOn ℝ ∞ (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) :=
    actualPiMixedCaps_lowering_smooth hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
      m hm Km hKm hmz i k (PiRoom δ) (hRawHOn k)
  have hE2On (i k : Fin 3) : ContDiffOn ℝ ∞ (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) :=
    actualPiMixedCaps_raising_smooth hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      m hm Km hKm hmz i k (PiRoom δ) (hRawLOn k)
  have hC1On (i k : Fin 3) : ContDiffOn ℝ ∞ (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) :=
    actualPiMixedCaps_lowering_mixed_smooth hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg
      G m hm Km hKm hmz i k (PiRoom δ) (hCaTOn i) hThOn (hE1On i k)
  have hC2On (i k : Fin 3) : ContDiffOn ℝ ∞ (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ) :=
    actualPiMixedCaps_raising_mixed_smooth hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
      m hm Km hKm hmz i k (PiRoom δ) (hCASOn i) hShOn (hE2On i k)
  have hCaps := actualPiMixedCaps_common_cap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg
    G m hm Km hKm hmz δ hSK hSU hE1On hE2On hC1On hC2On
  refine ⟨δ,hδ,(min_le_left _ _).trans hδAρ,hSubA.trans hRoomA,G,
    fun j => (hGOn j).mono hSubA,fun j p hp v => hGlow j p (hSubA hp) v,
    m,hm,Km,hKm,hmz,?_,fun i k => ⟨hE1On i k,hE2On i k,hC1On i k,hC2On i k⟩,hCaps⟩
  -- the graphs, on the same witnesses
  intro i k p hp ell hell Q
  have hpA := hSubA hp
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hRoomA p hpA
  have hId : natH Q = PiH k (p,ell) ∧ natL (low Q) = PiL k (p,ell) ∧
      natN (low Q) = PiN k (p,ell) :=
    (hGerm k (p,ell) (Set.mk_mem_prod (hSubP hp) hell)).self_of_nhds
  obtain ⟨hIdH,hIdL,hIdN⟩ := hId
  have hEa (u : Hi) := loweringPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hreg hg hKernel lam Lam Q i p.1 hpA.1 p.2.1 hpA.2.1 (hG0 p hp) u
  have hEA (v : Half) := raisingPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hreg hKernel lam Lam Q i p.1 hpA.1 p.2.1 hpA.2.1 (hG0 p hp) v
  refine ⟨⟨hIdH,hIdL,hIdN⟩,?_,?_,?_,?_⟩
  · intro u
    exact (hEa u).trans (congrArg₂
      (fun (PH : Hi →L[ℝ] Hi) (PL : Half →L[ℝ] Half) =>
        loweringHigh hF hO hD i (PH u) - PL (loweringHigh hF hO hD i u)) hIdH hIdL)
  · intro v
    exact (hEA v).trans (congrArg₂
      (fun (PN : NegH →L[ℝ] NegH) (PL : Half →L[ℝ] Half) =>
        PN (raisingLow hF hO hD i v) - raisingLow hF hO hD i (PL v)) hIdN hIdL)
  · intro u
    have hMixed := mixed_lowering_cancellation IH JL (CaT G i p) (Th p) (Tl p) (natH Q) (natL (low Q))
      (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q i p.1 p.2.1)
      (loweringHigh hF hO hD i) (loweringLow hF hO hD i)
      (fun x => (hCaT i).1 p hpA x)
      (fun x => by
        simpa only [adjointHighRemainder, adjointHalfRemainder, ContinuousLinearMap.comp_apply] using
          (congrArg (fun A : Hi →L[ℝ] NegH => A x)
            (referenceAdjointRadialSecondRemainder_high_half_compatibility
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2 hSeg)))
      hEa u
    exact hMixed.trans (congrArg₂
      (fun (PH : Hi →L[ℝ] Hi) (PL : Half →L[ℝ] Half) =>
        loweringLow hF hO hD i (Th p (PH u)) - Tl p (PL (loweringHigh hF hO hD i u))) hIdH hIdL)
  · intro u
    have hMixed := mixed_raising_cancellation JL (CAS i p) (ShS p) (SlS p) (natL (low Q)) (natN (low Q))
      (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q i p.1 p.2.1)
      (raisingHigh hF hO hD i) (raisingLow hF hO hD i)
      (fun x => (hCAS i).1 p hpA x)
      (fun x => congrArg (fun A : Half →L[ℝ] NegH => A x)
        (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (low Q)))
      hEA u
    exact hMixed.trans (congrArg₂
      (fun (PN : NegH →L[ℝ] NegH) (PL : Half →L[ℝ] Half) =>
        PN (SlS p (raisingHigh hF hO hD i u)) - raisingLow hF hO hD i (PL (ShS p u))) hIdN hIdL)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v015_exists_iteratedFDerivWithin_cap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.exists_reference_commonRadius_actualPi_mixed_graph_caps
