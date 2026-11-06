import Calderon.ActualReferenceTwoAngleAdjointMidpointCore
import Calderon.ActualReferenceTwoAngleLowerRadialEndpoint
import Calderon.NativeLowerTransposeDerivative

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-midpoint-topology-v109.md. Genuine same normed transpose. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
local instance : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (i j k l : Fin 3)

lemma contDiffAt_referenceTwoAngleAdjointHalfRadialFamily_of_original
    (p : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.2.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p.2.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) p := by
  have hLow := contDiffAt_referenceTwoAngleLowerRadialEndpointFamily_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l p hNormal hWeak
  letI : NormedAddCommGroup
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let t : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := sphereLowerDistributionalTranspose
      map_add' := fun A B => by
        have h := sphereLowerDistributionalTransposeL.map_add A B
        simpa only [sphereLowerDistributionalTransposeL_apply] using h
      map_smul' := fun c A => by
        have h := sphereLowerDistributionalTransposeL.map_smul c A
        simpa only [sphereLowerDistributionalTransposeL_apply,RingHom.id_apply] using h }
  have hBound : ∀ A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)),
      ‖t A‖ ≤ (1 : ℝ) * ‖A‖ := by
    intro A
    have hAdj : t A = ContinuousLinearMap.adjoint A := by
      change sphereLowerDistributionalTranspose A = ContinuousLinearMap.adjoint A
      unfold sphereLowerDistributionalTranspose sphereHalfDualCarrierEquiv
      apply ContinuousLinearMap.ext
      intro u
      rfl
    have hNorm : ‖t A‖ ≤ ‖A‖ :=
      (congrArg (fun B : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => ‖B‖) hAdj).le.trans
          (ContinuousLinearMap.adjoint.norm_map A).le
    simpa only [one_mul] using hNorm
  let Tnorm : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      t (1 : ℝ) hBound
  have hApply (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
      Tnorm A = sphereLowerDistributionalTranspose A := rfl
  have hSmooth := Tnorm.contDiff.contDiffAt.comp p hLow
  apply hSmooth.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t =>
    (hApply (referenceTwoAngleLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)).symm)

lemma contDiffOn_referenceTwoAngleAdjointMidpointRadialFamily
    (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceTwoAngleAdjointMidpointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l)
      (referenceTwoAngleRadialInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) := by
  let Ω := referenceTwoAngleRadialInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l
  have hLow : ContDiffOn ℝ ∞ (referenceTwoAngleAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) Ω := by
    intro t ht
    have hOrig := ht.1.2.2
    exact (contDiffAt_referenceTwoAngleAdjointHalfRadialFamily_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hOrig.2.2 hOrig.2.1).contDiffWithinAt
  have hHigh := (contDiffOn_referenceTwoAngleAdjointThreeHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l hreg).mono
      (show Ω ⊆ Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) from fun _ ht => ht.1)
  have hPair : ContDiffOn ℝ ∞ (referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) Ω := hLow.prodMk hHigh
  exact contDiffOn_sphereSobolevCompatibleInterpolationFamily
    (referenceTwoAngleAdjointRadialEndpointPairFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) Ω
    (isOpen_referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleAdjointRadialEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l) hPair

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleAdjointHalfRadialFamily_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleAdjointMidpointRadialFamily
