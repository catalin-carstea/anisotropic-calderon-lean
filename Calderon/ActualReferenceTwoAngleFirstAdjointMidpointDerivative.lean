import Calderon.ActualReferenceTwoAngleAdjointMidpointTopology
import Calderon.ActualReferenceTwoAngleFirstMidpointDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Calderon.LocalRadialDerivative

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-first-adjoint-derivative-pair-v110.md. Actual genuine first-angle derivative. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
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

attribute [local irreducible] referenceTwoAngleAdjointMidpointRadialFamily
  referenceTwoAngleRadialInvertibleLocus

def referenceTwoAngleFirstAdjointMidpointDerivativeFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (z : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialFirstDerivative
    (fun t : (ℝ × (ℝ × (R3 × ℝ))) × ℝ => referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))) (z,0)

lemma hasDerivAt_referenceTwoAngleAdjointMidpoint_first_angle
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    HasDerivAt (fun θ : ℝ => referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (θ,(φ,p)))
      (referenceTwoAngleFirstAdjointMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (φ,p)) 0 := by
  let F : (ℝ × (ℝ × (R3 × ℝ))) × ℝ → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    fun t => referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))
  have hM := (contDiffOn_referenceTwoAngleAdjointMidpointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l hreg).contDiffAt
      ((isOpen_referenceTwoAngleRadialInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).mem_nhds hp)
  have hF : ContDiffAt ℝ ∞ F ((φ,p),0) :=
    hM.comp ((φ,p),0) (contDiffAt_snd.prodMk (contDiffAt_fst.fst.prodMk contDiffAt_fst.snd))
  have hc : HasDerivAt (fun θ : ℝ => ((φ,p),θ)) (0,1) 0 :=
    (hasDerivAt_const 0 (φ,p)).prodMk (hasDerivAt_id 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only [Function.comp_def,referenceTwoAngleFirstAdjointMidpointDerivativeFamily,radialFirstDerivative,F] using hd

lemma contDiffAt_referenceTwoAngleFirstAdjointMidpointDerivativeFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hp : (0,(z.1,z.2)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    ContDiffAt ℝ ∞ (referenceTwoAngleFirstAdjointMidpointDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l) z := by
  let F : (ℝ × (ℝ × (R3 × ℝ))) × ℝ → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    fun t => referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (t.2,(t.1.1,t.1.2))
  have hM := (contDiffOn_referenceTwoAngleAdjointMidpointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l hreg).contDiffAt
      ((isOpen_referenceTwoAngleRadialInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).mem_nhds hp)
  have hF : ContDiffAt ℝ ∞ F (z,0) :=
    hM.comp (z,0) (contDiffAt_snd.prodMk (contDiffAt_fst.fst.prodMk contDiffAt_fst.snd))
  exact (contDiffAt_radialFirstDerivative F (z,0) hF).comp z
    (contDiffAt_id.prodMk contDiffAt_const)

lemma inner_probability_referenceTwoAngleFirstMidpointDerivative_adjoint
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (referenceTwoAngleFirstMidpointDerivativeFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p) u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm
        (referenceTwoAngleFirstAdjointMidpointDerivativeFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (φ,p) v)⟫_ℝ := by
  let M : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun θ =>
    referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
  let MA : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun θ =>
    referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (θ,(φ,p))
  let K := referenceTwoAngleFirstMidpointDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p)
  let KA := referenceTwoAngleFirstAdjointMidpointDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (φ,p)
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  have hM : HasDerivAt M K 0 := hasDerivAt_referenceTwoAngleMidpoint_first_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l φ p hp
  have hMA : HasDerivAt MA KA 0 := hasDerivAt_referenceTwoAngleAdjointMidpoint_first_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l φ p hp
  have hLeft : HasDerivAt (fun θ : ℝ => ⟪M θ u,I v⟫_ℝ) ⟪K u,I v⟫_ℝ 0 := by
    simpa only [map_zero,add_zero,zero_add,inner_zero_right] using
      (hM.clm_apply (hasDerivAt_const (0:ℝ) u)).inner ℝ (hasDerivAt_const (0:ℝ) (I v))
  have hRight : HasDerivAt (fun θ : ℝ => ⟪I u,MA θ v⟫_ℝ) ⟪I u,KA v⟫_ℝ 0 := by
    simpa only [map_zero,add_zero,inner_zero_left,zero_add] using
      (hasDerivAt_const (0:ℝ) (I u)).inner ℝ (hMA.clm_apply (hasDerivAt_const (0:ℝ) v))
  have hNear : ∀ᶠ θ : ℝ in 𝓝 0, (θ,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l :=
    (continuousAt_id.prodMk continuousAt_const).eventually
      ((isOpen_referenceTwoAngleRadialInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).mem_nhds hp)
  have hCurve : (fun θ : ℝ => ⟪M θ u,I v⟫_ℝ) =ᶠ[𝓝 0]
      (fun θ : ℝ => ⟪I u,MA θ v⟫_ℝ) := by
    filter_upwards [hNear] with θ hθ
    have hPair := inner_probability_referenceTwoAngleMidpointRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l (θ,(φ,p)) hθ u v
    exact ((Z.symm.inner_map_map (M θ u) (I v)).symm).trans
      (hPair.trans (Z.symm.inner_map_map (I u) (MA θ v)))
  have hNative : ⟪K u,I v⟫_ℝ=⟪I u,KA v⟫_ℝ :=
    (hLeft.congr_of_eventuallyEq hCurve.symm).unique hRight
  exact (Z.symm.inner_map_map (K u) (I v)).trans
    (hNative.trans (Z.symm.inner_map_map (I u) (KA v)).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFirstAdjointMidpointDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceTwoAngleAdjointMidpoint_first_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleFirstAdjointMidpointDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_probability_referenceTwoAngleFirstMidpointDerivative_adjoint
