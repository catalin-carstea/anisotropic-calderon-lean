import Calderon.ActualNativeMovingHighLocalRemainderSmoothness
import Calderon.ActualJacobiNativeMultiplierProfileLocalSmoothness
import Calderon.ActualFinitePairedRadialQuarticDomain
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referenceHighAdjointWeightedQuotientOpenIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceRadialEndpointInvertibleLocus

theorem contDiffOn_referenceHighAdjointMovingDifferenceQuotient_weighted_open_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ Ω ∧ χ y ∈ V}
    IsOpen U ∧ ∀ power : ℕ, ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (fun y => (R y)^power •
        referenceHighAdjointMovingDifferenceQuotient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_WEIGHTED_QUOTIENT_OPEN_BODY"
    out.flush
  intro Ω V χ U
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hJacobi := exists_referenceJacobiNativeMultiplier_profile_open_room
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hV : IsOpen V := hJacobi.1
  have hχ : Continuous χ :=
    continuous_const.prodMk (continuous_id.prodMk hR.continuous)
  have hNonzero : IsOpen {y : R3 | R y ≠ 0} :=
    isOpen_ne_fun hR.continuous continuous_const
  have hU : IsOpen U := hNonzero.inter ((hΩ.preimage hχ).inter (hV.preimage hχ))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_WEIGHTED_QUOTIENT_INVERSE_REGION_OPEN"
    out.flush
  refine ⟨hU,?_⟩
  intro power i
  have hQuotient : ContDiffOn ℝ ∞ (fun y =>
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U := by
    intro y hy
    exact (contDiffAt_referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i
      hR.contDiffAt hy.1 hy.2.2 hy.2.1).contDiffWithinAt
  have hPower : ContDiffOn ℝ ∞ (fun y => (R y)^power) U := (hR.pow power).contDiffOn
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_WEIGHTED_QUOTIENT_OPEN_RESULT"
    out.flush
  exact hPower.smul hQuotient

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceHighAdjointMovingDifferenceQuotient_weighted_open_room
