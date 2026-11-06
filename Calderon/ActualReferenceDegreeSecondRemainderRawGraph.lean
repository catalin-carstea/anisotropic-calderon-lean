import Calderon.ActualReferenceDegreeHalfChosenNamedRadialHighGraph
import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.SignedTaylorOperatorDifference

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError

local instance referenceDegreeR2RawGraphHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceDegreeR2RawGraphNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

lemma referenceRadialDegreeCommutatorHalfSecondRemainder_raw_degree_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Bhigh := sphereSobolevShiftedDegreeL (3/2 : ℝ)
    let Bhalf := sphereSobolevShiftedDegreeL (1/2 : ℝ)
    let C2 := referenceRadialDegreeCommutatorHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Sh := referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Sl := referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    ∀ u : SphereSobolev (3/2 : ℝ),
      C2 (I u) = Bhalf (Sh u) - Sl (Bhigh u) := by
  intro I Bhigh Bhalf C2 Sh Sl
  let Fs : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Fl : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun t =>
    referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hParam (θ : ℝ) : ContDiffAt ℝ ∞ (fun t : ℝ => (q,(y,t))) (θ*r) :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
  have hFs (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ Fs (θ*r) :=
    (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (q,(y,θ*r)) (hSegment θ hθ).1).comp
      (f := fun t : ℝ => (q,(y,t))) (θ*r) (hParam θ)
  have hFl (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ Fl (θ*r) :=
    (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (q,(y,θ*r)) (hSegment θ hθ).2.2 (hSegment θ hθ).2.1).comp
      (f := fun t : ℝ => (q,(y,t))) (θ*r) (hParam θ)
  have hDifference := secondTaylorRemainder_operator_difference
    Fs Fl Bhigh Bhalf r hFs hFl
  have hCurve : (fun t : ℝ => Bhalf.comp (Fs t) - (Fl t).comp Bhigh) =
      (fun t : ℝ => referenceRadialDegreeCommutatorHighL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) := by
    funext t
    dsimp only [referenceRadialDegreeCommutatorHighL,Fs,Fl,Bhalf,Bhigh]
  have hRaw : secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHighL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r =
      Bhalf.comp Sh - Sl.comp Bhigh :=
    (congrArg (fun F => secondTaylorRemainder F r) hCurve).symm.trans hDifference
  intro u
  have hNamed := referenceRadialDegreeCommutatorHalfSecondRemainder_high_graph_on_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment u
  have hValue : (secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHighL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) u =
      Bhalf (Sh u) - Sl (Bhigh u) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
      hRaw
  exact hNamed.trans hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfSecondRemainder_raw_degree_graph
