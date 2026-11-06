import Calderon.ActualFiniteHarmonicProductRadialRemainderGraph
import Calderon.ActualFiniteGaugeAdjointRemainderGraph

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
PAIRED-FINITE-GENUINE-SIGNED-REMAINDER-DOMAIN-EXPANSION-v001.md. Exact uncompressed finite-input witnesses. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

attribute [local irreducible] harmonicSphereSubspace

attribute [local irreducible] secondTaylorRemainder referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL sphereSobolevPartialSum

local instance referenceFiniteGaugePairedRadialRemainderDomainHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteGaugePairedRadialRemainderDomainHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance pairedRemainderOperatorGroup : NormedAddCommGroup
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)

local instance pairedRemainderOperatorSpace : NormedSpace ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
    (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)

local instance referenceFiniteGaugePairedRadialRemainderDomainHighToHalfOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance





def referencePairedRadialSecondRemainderGraph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3) (r : ℝ)
    (v : SphereSobolev (3/2 : ℝ)) : Prop :=
  ∃ su tu : SphereSobolev (3/2 : ℝ),
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) su =
      (secondTaylorRemainder (V := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
        (fun t : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).toFun
          v ∧
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) tu =
      (secondTaylorRemainder (V := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
        (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).toFun
          v

attribute [local irreducible] referencePairedRadialSecondRemainderGraph

include hg in
set_option diagnostics true in
theorem exists_reference_commonRadius_finitePairedRadialSecondRemainder_domain
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
          let v : SphereSobolev (3/2 : ℝ) :=
            nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
              (sphereSobolevPartialSum (3/2 : ℝ) n f)
          referencePairedRadialSecondRemainderGraph
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r v := by
  obtain ⟨δp,hδp,hδpρ,hPrimal⟩ :=
    exists_reference_commonRadius_finiteProductHighSecondRemainder_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
  obtain ⟨δa,hδa,hδaρ,G,hAdjoint⟩ :=
    exists_reference_commonRadius_finiteGaugeAdjointSecondRemainder_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0 hKernel
  refine ⟨min δp δa,lt_min hδp hδa,(min_le_left _ _).trans hδpρ,?_⟩
  intro q hq y hy r hr n Q f
  let su : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f
  let tu : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q q y r f
  unfold referencePairedRadialSecondRemainderGraph
  refine ⟨su,tu,?_,?_⟩
  · exact hPrimal q hq y hy r (hr.trans (min_le_left _ _)) n Q f
  · exact hAdjoint q hq y hy r (hr.trans (min_le_right _ _)) n Q f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePairedRadialSecondRemainderGraph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePairedRadialSecondRemainder_domain
