import Calderon.ActualReferenceSmoothMultiplierSecondTaylorSmoothness
import Calderon.ActualReferenceExtendedCenterInverseRoom
import Calderon.CompactInverseDerivativeBounds
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
abbrev RadialPrimalJetParameter := (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)

def radialPrimalCommutatorUniformJetsTarget
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : Prop :=
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
    ∀ (m : RadialPrimalJetParameter × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
      (Km : Set R3) (hKm : IsCompact Km)
      (hmz : ∀ t x, x ∉ Km → m (t,x) = 0)
      (Kt : Set RadialPrimalJetParameter) (hKt : IsCompact Kt) (N : ℕ),
    let GS : ((ℝ × (R3 × ℝ)) × RadialPrimalJetParameter) →
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun z =>
      secondTaylorRemainder (fun tau : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2)
          (z.1.1,(z.1.2.1,tau))) z.1.2.2
    let GN : ((ℝ × (R3 × ℝ)) × RadialPrimalJetParameter) →
        SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      fun z => -realHalfOperatorAdjointL (GS z)
    let K : Set ((ℝ × (R3 × ℝ)) × RadialPrimalJetParameter) :=
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ Kt
    (∀ z ∈ K, ContDiffAt ℝ ∞ GS z ∧ ContDiffAt ℝ ∞ GN z) ∧
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ n GS z‖ ≤ Cg ∧ ‖iteratedFDeriv ℝ n GN z‖ ≤ Cg

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
