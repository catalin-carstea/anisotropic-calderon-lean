import Calderon.ActualReferenceRotationAdjointMidpointRadialFamily
import Mathlib.Analysis.Calculus.ContDiff.Comp
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3)
attribute [local irreducible] referenceRotationAdjointMidpointRadialFamily

def referenceAdjointMidpointAngleDerivativeFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  fderiv ℝ (referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hreg hF hO hD τ0 i j) (0,p) (1,0)

lemma referenceAdjointMidpointAngleDerivativeFamily_eq_deriv
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j p =
      deriv (fun θ : ℝ => referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hreg hF hO hD τ0 i j (θ,p)) 0 := by
  let M := referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j
  have hM : ContDiffAt ℝ ∞ M (0,p) :=
    contDiffAt_referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0 i j (0,p) ⟨mem_univ _,hp⟩
  have hc : HasDerivAt (fun θ : ℝ => (θ,p)) (1,0) 0 :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) p)
  change fderiv ℝ M (0,p) (1,0) = deriv (fun θ : ℝ => M (θ,p)) 0
  exact ((hM.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc).deriv.symm

lemma contDiffOn_referenceAdjointMidpointAngleDerivativeFamily_invertibleLocus :
    ContDiffOn ℝ ∞
      (referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let M := referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ Ω) :=
    contDiffOn_referenceRotationAdjointMidpointRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0 i j
  have hDM : ContDiffOn ℝ ∞ (fderiv ℝ M) (Set.univ ×ˢ Ω) :=
    hM.fderiv_of_isOpen (isOpen_univ.prod hΩ) (by simp)
  have hEval : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × (R3 × ℝ)) => fderiv ℝ M z (1,0)) (Set.univ ×ˢ Ω) :=
    hDM.clm_apply contDiffOn_const
  change ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) => fderiv ℝ M (0,p) (1,0)) Ω
  exact hEval.comp (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨mem_univ _,hp⟩)

lemma contDiffAt_referenceAdjointMidpointAngleDerivativeFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞
      (referenceAdjointMidpointAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j) p :=
  (contDiffOn_referenceAdjointMidpointAngleDerivativeFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
    hcalc hreg hF hO hD τ0 i j).contDiffAt
    ((isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMidpointAngleDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMidpointAngleDerivativeFamily_eq_deriv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointMidpointAngleDerivativeFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointMidpointAngleDerivativeFamily
