import Calderon.ActualAngularMixedEndpointPrimitives
import Calderon.ActualAngularPiMixedLowDraft
import Calderon.ActualMovingBoundaryTransposeIdentification
import Calderon.NativeRadialJetTranspose
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.SphereSobolevHalfDualRotationPairing
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeOrderOneCoefficientMultiplier

/-! DRAFT NOT CHECKED (claude-actual-Pi-low-instantiation-2026-10-29-v017, Claude Opus 5.5, author
only, nothing compiled or run). Before-source mathematics: output/MATHEMATICS.md. Root supplied the
routing and the exact API names. v015 (`ActualAngularPiMixedCapsDraft`) and v016
(`ActualAngularPiMixedLowDraft`) are imported unchanged.

Contents:
* §1 Lemma H: the half-level adjunction `P(x, aL_i y) = P(y, AL_i x)` for ALL `x y : Half`.
* §2 Lemma I: the inclusion graphs `J ∘ aH_i = aL_i ∘ IH` and `J ∘ AH_i = AL_i ∘ IH`.
* §3 the cross adjunctions (aA1), (aA2).
* §4 the native Pi primitives (high/half, half/negative, direct adjoint pairing).
* §5 the ACTUAL theorem. It obtains the v015 witnesses once and returns the v015 facts together
  with two actual low families `C_l, D_l` on the SAME witnesses: graphs, weak transpose graphs,
  midpoint norms, `ContDiffOn ∞` on the closed `S`, and one cap per `N`.
NOT claimed: D_Q, absorption, coercivity, Main. -/
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
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

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

-- actualSol: keep exact checked operator implementations opaque during elaboration.
attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevLinearCoordinateMulL
  rawAdjointMultiplierZero rawHalfMultiplierZero rotationJets commonSupportCoefficientFamily
  adjointHighRemainder adjointHalfRemainder sharpRemainder lowerSharpRemainder
  loweringAngularHighCommutator raisingCommutator
  loweringPiGain raisingPiGain loweringMixed raisingMixed

/-! ### §5 The ACTUAL theorem on the SAME v015 witnesses -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity) (hg : IsAdmissibleMetric g)
  (hKernel : UnitBallValueTraceKernel τ0)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ShS" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SlS" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "EaPiMap" => v015LoweringPiGainMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "EPiAMap" => v015RaisingPiGainMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaTPiMap" => v015LoweringMixedMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
  hreg hg
local notation "CPiSAMap" => v015RaisingMixedMap hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
  hreg
local notation "PiRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

include hreg in
private lemma actualPiMixedLow_pointwise_adjunction
    (Q : SmoothCoefficientJets 3) (i k : Fin 3) (p : Pphys) (ell : R3 →L[ℝ] ℝ)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω)
    (hIdH : natH Q = PiH k (p,ell))
    (hIdL : natL (low Q) = PiL k (p,ell))
    (hIdN : natN (low Q) = PiN k (p,ell))
    (Ch Dh : Hi →L[ℝ] Half)
    (hC : ∀ u, JL (Ch u) = loweringLow hF hO hD i (Th p (PiH k (p,ell) u)) -
      Tl p (PiL k (p,ell) (loweringHigh hF hO hD i u)))
    (hDgraph : ∀ v, JL (Dh v) = PiN k (p,ell) (SlS p (raisingHigh hF hO hD i v)) -
      raisingLow hF hO hD i (PiL k (p,ell) (ShS p v)))
    (u vTest : Hi) : PP (IH vTest) (JL (Ch u)) = PP (IH u) (JL (Dh vTest)) := by
  have hPic : ∀ x : Hi, IH (PiH k (p,ell) x) = PiL k (p,ell) (IH x) := by
    intro x
    exact (congrArg (fun A : Hi →L[ℝ] Hi => IH (A x)) hIdH).symm.trans
      ((v017_native_high_half hcalc hF hO hD τ0 Q x).trans
        (congrArg (fun A : Half →L[ℝ] Half => A (IH x)) hIdL))
  have hPiN : ∀ y : Half, JL (PiL k (p,ell) y) = PiN k (p,ell) (JL y) := by
    intro y
    exact (congrArg (fun A : Half →L[ℝ] Half => JL (A y)) hIdL).symm.trans
      ((v017_native_half_negative hcalc hF hO hD τ0 (low Q) y).trans
        (congrArg (fun A : NegH →L[ℝ] NegH => A (JL y)) hIdN))
  have hPis : ∀ (x : Half) (y : NegH), PP (PiL k (p,ell) x) y = PP x (PiN k (p,ell) y) := by
    intro x y
    exact (congrArg (fun A : Half →L[ℝ] Half => PP (A x) y) hIdL).symm.trans
      ((v017_native_pairing hcalc hF hO hD τ0 (low Q) x y).trans
        (congrArg (fun A : NegH →L[ℝ] NegH => PP x (A y)) hIdN))
  have hTc : ∀ z : Hi, JL (Th p z) = Tl p (IH z) :=
    v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p hSeg
  have hSc : ∀ z : Hi, SlS p (IH z) = JL (ShS p z) :=
    v016_actual_Sh_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData p hSeg
  exact v016_mixed_adjunction_of_primitives
    (loweringLow hF hO hD i) (raisingLow hF hO hD i) (Tl p) (SlS p)
    (loweringHigh hF hO hD i) (raisingHigh hF hO hD i) (Th p) (ShS p)
    Ch Dh
    (PiH k (p,ell)) (PiL k (p,ell)) (PiN k (p,ell))
    hC hDgraph (v017_aA1 hF hO hD i) (v017_aA2 hF hO hD i) v016_pairing_inclusion_symm
    hTc hSc
    (v016_actual_pairing_Sl_Tl hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData p hSeg)
    hPic hPiN hPis u vTest

include hreg hg hKernel in
/-- ACTUAL mixed Pi low endpoints. The v015 witnesses `δ, G, m, Km` are obtained ONCE. The v015
facts are returned unchanged, together with two actual low families `C_l, D_l : Half → Neg` on
`S = commonRoom δ × closedBall 0 1`, bound to the SAME witnesses. -/
theorem exists_reference_commonRadius_actualPi_mixed_low_graph_caps :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ)) ∧
      (∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ v : Half,
        JL (G j p v) = Tl p ((Ml j) v) - (Mn j) (Tl p v)) ∧
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ k, ContDiff ℝ ∞ (m k)) (Km : Set R3)
      (hKm : IsCompact Km) (hmz : ∀ k t x, x ∉ Km → m k (t,x) = 0),
      -- v015 facts, unchanged
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
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i k : Fin 3, ∀ n : ℕ, n ≤ N → ∀ z ∈ PiRoom δ,
        ‖iteratedFDerivWithin ℝ n (EaPiMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EPiAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CaTPiMap G m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (CPiSAMap m hm Km hKm hmz i k) (PiRoom δ) z‖ ≤ M) ∧
      -- v017: actual low families on the SAME witnesses
      ∃ Cl Dl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] NegH,
        (∀ i k : Fin 3,
          ContDiffOn ℝ ∞ (Cl i k) (PiRoom δ) ∧ ContDiffOn ℝ ∞ (Dl i k) (PiRoom δ)) ∧
        (∀ i k : Fin 3, ∀ z ∈ PiRoom δ,
          (∀ u w : Hi, PP (IH w) (JL (CaTPiMap G m hm Km hKm hmz i k z u)) =
            PP (IH u) (JL (CPiSAMap m hm Km hKm hmz i k z w))) ∧
          (Cl i k z).comp IH = (JL).comp (CaTPiMap G m hm Km hKm hmz i k z) ∧
          (I33).comp (Cl i k z) =
            (v016TransposeL (CPiSAMap m hm Km hKm hmz i k z)).comp JL ∧
          ‖Cl i k z‖ ≤ (‖CaTPiMap G m hm Km hKm hmz i k z‖ +
            ‖CPiSAMap m hm Km hKm hmz i k z‖) / 2 ∧
          (Dl i k z).comp IH = (JL).comp (CPiSAMap m hm Km hKm hmz i k z) ∧
          (I33).comp (Dl i k z) =
            (v016TransposeL (CaTPiMap G m hm Km hKm hmz i k z)).comp JL ∧
          ‖Dl i k z‖ ≤ (‖CaTPiMap G m hm Km hKm hmz i k z‖ +
            ‖CPiSAMap m hm Km hKm hmz i k z‖) / 2) ∧
        ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i k : Fin 3, ∀ n : ℕ, n ≤ N → ∀ z ∈ PiRoom δ,
          ‖iteratedFDerivWithin ℝ n (Cl i k) (PiRoom δ) z‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Dl i k) (PiRoom δ) z‖ ≤ M := by
  -- v015 witnesses obtained ONCE
  have hCapsOwner := exists_reference_commonRadius_actualPi_mixed_graph_caps
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  obtain ⟨δ,hδ,hδρ,hRoom,G,hGOn,hGlow,m,hm,Km,hKm,hmz,hGraph,hSmooth,hCaps⟩ := hCapsOwner
  have hρ : 0 < ρ := hData.1.2.1
  have hSK : IsCompact (PiRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hSU : UniqueDiffOn ℝ (PiRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hρ hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  -- the actual mixed adjunction at the CURRENT z (MATHEMATICS.md §6); no new premise
  have hAdj : ∀ i k : Fin 3, ∀ z ∈ PiRoom δ, ∀ u w : Hi,
      PP (IH w) (JL (CaTPiMap G m hm Km hKm hmz i k z u)) =
        PP (IH u) (JL (CPiSAMap m hm Km hKm hmz i k z w)) := by
    intro i k z hz u vTest
    obtain ⟨p,ell⟩ := z
    have hp : p ∈ commonRoom y0 ρ δ := hz.1
    have hell : ell ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1 := hz.2
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      hRoom p hp
    have hAt := hGraph i k p hp ell hell
    exact actualPiMixedLow_pointwise_adjunction hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg
      (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (p,ell)) i k p ell hSeg
      hAt.1.1 hAt.1.2.1 hAt.1.2.2
      (CaTPiMap G m hm Km hKm hmz i k (p,ell)) (CPiSAMap m hm Km hKm hmz i k (p,ell))
      hAt.2.2.2.1 hAt.2.2.2.2 u vTest
  -- the two low families, via v016's generic smooth-family theorem on the SAME closed S
  have hLow := fun i k : Fin 3 =>
    v016_exists_contDiffOn_lowEndpoint (PiRoom δ) hSU
      (CaTPiMap G m hm Km hKm hmz i k) (CPiSAMap m hm Km hKm hmz i k)
      (hSmooth i k).2.2.1 (hSmooth i k).2.2.2 (hAdj i k)
  choose Cl hCl using hLow
  have hLowSwap := fun i k : Fin 3 =>
    v016_exists_contDiffOn_lowEndpoint (PiRoom δ) hSU
      (CPiSAMap m hm Km hKm hmz i k) (CaTPiMap G m hm Km hKm hmz i k)
      (hSmooth i k).2.2.2 (hSmooth i k).2.2.1
      (fun z hz => v016_adjunction_swap _ _ (hAdj i k z hz))
  choose Dl hDl using hLowSwap
  refine ⟨δ,hδ,hδρ,hRoom,G,hGOn,hGlow,m,hm,Km,hKm,hmz,hGraph,hSmooth,hCaps,Cl,Dl,
    fun i k => ⟨(hCl i k).1,(hDl i k).1⟩,?_,
    fun N => v016_exists_uniform_cap_two (PiRoom δ) hSK hSU Cl Dl
      (fun i k => (hCl i k).1) (fun i k => (hDl i k).1) N⟩
  intro i k z hz
  have hCAt := (hCl i k).2 z hz
  have hDAt := (hDl i k).2 z hz
  exact ⟨hAdj i k z hz,hCAt.1,hCAt.2.1,
    hCAt.2.2.2.trans_eq (congrArg (fun r : ℝ => r / 2) (add_comm _ _)),
    hDAt.1,hDAt.2.1,hDAt.2.2.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v017_pairing_loweringLow_raisingLow
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v017_inclusion_loweringHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v017_inclusion_raisingHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v017_native_pairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.exists_reference_commonRadius_actualPi_mixed_low_graph_caps
