import Calderon.ActualReferenceTwoAngleMidpointTrace
import Calderon.LocalRadialDerivative

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-first-midpoint-derivative-v026.md. Actual fixed first-angle derivative. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open Filter
open scoped Topology

open SphereHarmonic

attribute [local irreducible] referenceTwoAngleSharpMidpointRadialTraceFamily
  referenceTwoAngleRadialInvertibleLocus

def referenceTwoAngleFirstMidpointDerivativeFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (z : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialFirstDerivative
    (fun t : (ℝ × (ℝ × (R3 × ℝ))) × ℝ => referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))) (z,0)

lemma hasDerivAt_referenceTwoAngleMidpoint_first_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    HasDerivAt (fun θ : ℝ => referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p)))
      (referenceTwoAngleFirstMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p)) 0 := by
  let F : (ℝ × (ℝ × (R3 × ℝ))) × ℝ → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    fun t => referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))
  have hM := contDiffAt_referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p)) hp
  have hF : ContDiffAt ℝ ∞ F ((φ,p),0) :=
    hM.comp ((φ,p),0) (contDiffAt_snd.prodMk (contDiffAt_fst.fst.prodMk contDiffAt_fst.snd))
  have hc : HasDerivAt (fun θ : ℝ => ((φ,p),θ)) (0,1) 0 :=
    (hasDerivAt_const 0 (φ,p)).prodMk (hasDerivAt_id 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only [Function.comp_def,referenceTwoAngleFirstMidpointDerivativeFamily,radialFirstDerivative,F] using hd

lemma contDiffAt_referenceTwoAngleFirstMidpointDerivativeFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hp : (0,(z.1,z.2)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    ContDiffAt ℝ ∞ (referenceTwoAngleFirstMidpointDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) z := by
  let F : (ℝ × (ℝ × (R3 × ℝ))) × ℝ → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    fun t => referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))
  have hM := contDiffAt_referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(z.1,z.2)) hp
  have hF : ContDiffAt ℝ ∞ F (z,0) :=
    hM.comp (z,0) (contDiffAt_snd.prodMk (contDiffAt_fst.fst.prodMk contDiffAt_fst.snd))
  exact (contDiffAt_radialFirstDerivative F (z,0) hF).comp z
    (contDiffAt_id.prodMk contDiffAt_const)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFirstMidpointDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceTwoAngleMidpoint_first_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleFirstMidpointDerivativeFamily
