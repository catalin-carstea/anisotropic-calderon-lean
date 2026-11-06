import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.LocalSmoothSignedTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referencePairedHighRadialLocalSmoothnessHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedHighRadialLocalSmoothnessOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceFamily
  referenceAdjointThreeHalfRadialFamily referenceRadialEndpointInvertibleLocus
  secondTaylorRemainder referenceSharpRadialTraceSecondRemainder

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2) (q,(y,r)) ∧
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => secondTaylorRemainder
      (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2) (q,(y,r)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_HIGH_INPUT_BODY"
    out.flush
  let T : ((ℝ × R3) × ℝ) → ℝ × (R3 × ℝ) := fun z => (z.1.1,(z.1.2,z.2))
  let σ : (ℝ × (R3 × ℝ)) → (ℝ × R3) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  have hT : ContDiff ℝ ∞ T :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hσ : ContDiff ℝ ∞ σ :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Ωt : Set ((ℝ × R3) × ℝ) := T ⁻¹' Ω
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩt : IsOpen Ωt := hΩ.preimage hT.continuous
  have hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, ((q,y),θ*r) ∈ Ωt := hSegment
  let FS : ((ℝ × R3) × ℝ) → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (T z)
  have hFS : ContDiffOn ℝ ∞ FS Ωt := by
    intro z hz
    have hRaw := (contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        (hΩ.mem_nhds hz)
    exact (hRaw.comp z hT.contDiffAt).contDiffWithinAt
  have hRS := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    FS Ωt hΩt hFS (q,y) r hSeg
  have hCS : ContDiffAt ℝ ∞
      ((fun z : (ℝ × R3) × ℝ => secondTaylorRemainder
        (fun t : ℝ => FS (z.1,t)) z.2) ∘ σ) (q,(y,r)) :=
    hRS.comp (q,(y,r)) hσ.contDiffAt
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_HIGH_INPUT_S_TAYLOR_READY"
    out.flush
  let FA : ((ℝ × R3) × ℝ) → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (T z)
  have hFA : ContDiffOn ℝ ∞ FA Ωt := by
    intro z hz
    have hRaw := (contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        (hΩ.mem_nhds hz)
    exact (hRaw.comp z hT.contDiffAt).contDiffWithinAt
  have hRA := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    FA Ωt hΩt hFA (q,y) r hSeg
  have hCA : ContDiffAt ℝ ∞
      ((fun z : (ℝ × R3) × ℝ => secondTaylorRemainder
        (fun t : ℝ => FA (z.1,t)) z.2) ∘ σ) (q,(y,r)) :=
    hRA.comp (q,(y,r)) hσ.contDiffAt
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_HIGH_INPUT_A_TAYLOR_READY"
    out.flush
  constructor
  · simpa only [referenceSharpRadialTraceSecondRemainder,FS,T,σ,Function.comp_def] using hCS
  · simpa only [FA,T,σ,Function.comp_def] using hCA

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
