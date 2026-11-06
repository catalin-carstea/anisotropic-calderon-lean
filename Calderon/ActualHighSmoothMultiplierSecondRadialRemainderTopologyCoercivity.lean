import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderCoercivity
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualReferenceRadialEndpointOpenLocus

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-FIXED-MULTIPLIER-REMAINDER-TOPOLOGY-EXPANSION-v001.md. Independent multiplier parameter frozen in radial derivative. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
  (hmz : ∀ t x, x ∉ Km → m (t,x)=0)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder referenceStrongDriftFamily
  commonSupportCoefficientFamily
local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderTopologyComplete1 : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderTopologyComplete2 : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

lemma contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (t : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2) z.1.1 z.1.2.1 z.1.2.2) ((q,(y,r)),t) := by
  let Ω0 : Set (ℝ × (R3 × ℝ)) := {p |
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible ∧
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible}
  have hΩ0 : IsOpen Ω0 := by
    letI : CompleteSpace (StrongDirichletSpace 1) := instCompleteSpaceStrongDirichletSpace 1
    have hOne : IsOpen {p : ℝ × (R3 × ℝ) |
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible} :=
      ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
        (contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1).continuous
    exact hOne.inter (isOpen_referenceStrongDriftFamily_zero_invertible_set
      g L y0 Φ B ε C ρ H a w hData hcalc)
  let F : ((ℝ × R3) × T) × ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun z =>
    referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.1.2) (z.1.1.1,(z.1.1.2,z.2))
  let Ω : Set (((ℝ × R3) × T) × ℝ) := {z | (z.1.1.1,(z.1.1.2,z.2)) ∈ Ω0}
  have hΩ : IsOpen Ω := hΩ0.preimage
    (continuous_fst.fst.fst.prodMk (continuous_fst.fst.snd.prodMk continuous_snd))
  have hSmooth : ContDiffOn ℝ ∞ F Ω := by
    intro z hz
    have hPair :
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 z.1.1.1 (z.1.1.2,z.2)).IsInvertible ∧
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 z.1.1.1 (z.1.1.2,z.2)).IsInvertible := hz
    have hB := contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
        (z.1.1.1,(z.1.1.2,z.2)) z.1.2 hPair.1 hPair.2
    exact (hB.comp
      (f := fun u : ((ℝ × R3) × T) × ℝ => ((u.1.1.1,(u.1.1.2,u.2)),u.1.2)) z
      ((contDiffAt_fst.fst.fst.prodMk
        (contDiffAt_fst.fst.snd.prodMk contDiffAt_snd)).prodMk contDiffAt_fst.snd)).contDiffWithinAt
  have hR := contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ω hΩ hSmooth ((q,y),t) r hSegment
  simpa only [referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,Function.comp_def] using
    hR.comp (f := fun u : (ℝ × (R3 × ℝ)) × T => (((u.1.1,u.1.2.1),u.2),u.1.2.2)) ((q,(y,r)),t)
      (((contDiffAt_fst.fst.prodMk contDiffAt_fst.snd.fst).prodMk contDiffAt_snd).prodMk
        contDiffAt_fst.snd.snd)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
