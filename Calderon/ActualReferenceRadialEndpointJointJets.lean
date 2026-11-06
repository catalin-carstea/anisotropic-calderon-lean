import Calderon.ActualReferencePairedLowRadialRemainderLocalSmoothness
import Calderon.ActualReferencePrimalCommutatorJets
import Calderon.ActualReferenceRadialEndpointOpenLocus
/-! Source-only complete repair v002, not compiled by its author.
Upfront: /tmp/ActualReferenceRadialEndpointJointJetsRepair_v002_20261023.md.
The exact auxiliary target/public theorem type is unchanged. Cap construction
now occurs entirely in a geometry-free full-payload theorem, with explicit
existing canonical data arguments. No new hypothesis, instance or limit. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] harmonicSphereSubspace secondTaylorRemainder referenceSharpRadialTraceSecondRemainder
 referenceLowerRadialTraceSecondRemainder referenceRadialEndpointInvertibleLocus

/-- Full compact-jet payload, proved before introducing any geometry.
The explicit instance arguments below are the existing canonical instances;
no local instance or replacement structure is installed. -/
private lemma radialEndpointUniformJointJetPayload_of_isCompact
    (SH TH : Pphys → Hi →L[ℝ] Half)
    (SL TL : Pphys → Half →L[ℝ] Neg)
    (K : Set Pphys) (hK : IsCompact K)
    (hHigh : ∀ z ∈ K, ContDiffAt ℝ ∞ SH z ∧ ContDiffAt ℝ ∞ TH z)
    (hLow : ∀ z ∈ K, ContDiffAt ℝ ∞ SL z ∧ ContDiffAt ℝ ∞ TL z)
    (N : ℕ) :
    (∀ z ∈ K, (ContDiffAt ℝ ∞ SH z ∧ ContDiffAt ℝ ∞ TH z) ∧
      (ContDiffAt ℝ ∞ SL z ∧ ContDiffAt ℝ ∞ TL z)) ∧
    ∃ CE : ℝ, 0 < CE ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ K,
      (‖iteratedFDeriv ℝ n SH z‖ ≤ CE ∧ ‖iteratedFDeriv ℝ n TH z‖ ≤ CE) ∧
      (‖iteratedFDeriv ℝ n SL z‖ ≤ CE ∧ ‖iteratedFDeriv ℝ n TL z‖ ≤ CE) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_COLD_PACKAGE_HIGH_CAP"
    out.flush
  have hHighCaps := exists_pos_common_compact_iteratedFDeriv_bound
    SH TH K hK (fun z hz => (hHigh z hz).1) (fun z hz => (hHigh z hz).2) N
  let CH : ℝ := Classical.choose hHighCaps
  have hCH : 0 < CH := (Classical.choose_spec hHighCaps).1
  have hBHigh := (Classical.choose_spec hHighCaps).2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_COLD_PACKAGE_LOW_CAP"
    out.flush
  have hLowCaps := exists_pos_common_compact_iteratedFDeriv_bound
    SL TL K hK (fun z hz => (hLow z hz).1) (fun z hz => (hLow z hz).2) N
  let CL : ℝ := Classical.choose hLowCaps
  have hCL : 0 < CL := (Classical.choose_spec hLowCaps).1
  have hBLow := (Classical.choose_spec hLowCaps).2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_COLD_PACKAGE_ASSEMBLY"
    out.flush
  refine ⟨fun z hz => ⟨hHigh z hz, hLow z hz⟩, max CH CL,
    hCH.trans_le (le_max_left _ _), ?_⟩
  intro n hn z hz
  have hSH := (hBHigh n hn z hz).1
  have hTH := (hBHigh n hn z hz).2
  have hSL := (hBLow n hn z hz).1
  have hTL := (hBLow n hn z hz).2
  exact ⟨⟨hSH.trans (le_max_left _ _), hTH.trans (le_max_left _ _)⟩,
    ⟨hSL.trans (le_max_right _ _), hTL.trans (le_max_right _ _)⟩⟩

def radialEndpointUniformJointJetsTarget
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : Prop :=
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∀ N : ℕ,
    let SH : Pphys → Hi →L[ℝ] Half := fun z => referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let TH : Pphys → Hi →L[ℝ] Half := fun z => secondTaylorRemainder
      (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let SL : Pphys → Half →L[ℝ] Neg := fun z => referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let TL : Pphys → Half →L[ℝ] Neg := fun z => secondTaylorRemainder
      (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let K : Set Pphys := Set.prod (Icc (0 : ℝ) 1)
      (Set.prod (closedBall y0 ρ) (Icc (-d) d))
    (∀ z ∈ K, (ContDiffAt ℝ ∞ SH z ∧ ContDiffAt ℝ ∞ TH z) ∧
      (ContDiffAt ℝ ∞ SL z ∧ ContDiffAt ℝ ∞ TL z)) ∧
    ∃ CE : ℝ, 0 < CE ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ K,
      (‖iteratedFDeriv ℝ n SH z‖ ≤ CE ∧ ‖iteratedFDeriv ℝ n TH z‖ ≤ CE) ∧
      (‖iteratedFDeriv ℝ n SL z‖ ≤ CE ∧ ‖iteratedFDeriv ℝ n TL z‖ ≤ CE)

attribute [local irreducible] radialEndpointUniformJointJetsTarget

theorem exists_reference_radial_endpoint_uniform_joint_jets
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    radialEndpointUniformJointJetsTarget g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_START"
    out.flush
  classical
  have hFullJetPayload := radialEndpointUniformJointJetPayload_of_isCompact
  obtain ⟨d0, hd0, hd0ρ, hRoom⟩ :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_RADIUS"
    out.flush
  let d := min d0 1
  unfold radialEndpointUniformJointJetsTarget
  refine ⟨d, lt_min hd0 one_pos, (min_le_left _ _).trans hd0ρ,
    min_le_right _ _, ?_⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_UNFOLDED"
    out.flush
  intro N SH TH SL TL K
  have hSegment (z : Pphys) (hz : z ∈ K) : ∀ θ ∈ Icc (0 : ℝ) 1,
      (z.1,(z.2.1,θ*z.2.2)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    intro θ hθ
    have hr : |z.2.2| ≤ d0 := (abs_le.mpr hz.2.2).trans (min_le_left _ _)
    have hθr : |θ*z.2.2| ≤ d0 := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      calc θ*|z.2.2| ≤ 1*|z.2.2| :=
            mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)
        _ = |z.2.2| := one_mul _
        _ ≤ d0 := hr
    exact hRoom ⟨hz.1,hz.2.1,abs_le.mp hθr⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_SEGMENT"
    out.flush
  have hHigh (z : Pphys) (hz : z ∈ K) : ContDiffAt ℝ ∞ SH z ∧ ContDiffAt ℝ ∞ TH z :=
    contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
        z.1 z.2.1 z.2.2 (hSegment z hz)
  have hLow (z : Pphys) (hz : z ∈ K) : ContDiffAt ℝ ∞ SL z ∧ ContDiffAt ℝ ∞ TL z :=
    contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
        z.1 z.2.1 z.2.2 (hSegment z hz)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_SMOOTH"
    out.flush
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  -- All actual geometry has already been consumed in hHigh/hLow/hK.
  clear hSegment
  clear_value SH TH SL TL K
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ENDPOINT_JETS_FULL_PACKAGE_APPLY"
    out.flush
  -- No cap existential elimination or bound projection in the geometry context.
  exact hFullJetPayload SH TH SL TL K hK hHigh hLow N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
