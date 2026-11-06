import Calderon.ActualReferenceGaugeNormalHighCommutatorDefinition

/-! Full BEFORE-SOURCE v252: exact original five-root K3 package split at the
original constructor boundary. Actual native minus/right reciprocal retained. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceGaugeNormalHighCommutatorFamily
  referenceGaugeNormalHalfCommutatorFamily referenceGaugeNormalHighInvertibleLocus
  referenceHighSmoothMultiplierBoundaryCommutatorFamily referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalThreeHalfMultiplierFamily referenceGaugeNormalHalfMultiplierFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily

lemma referenceGaugeNormalHighCommutatorFamily_half_agreement
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceGaugeNormalHighCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) =
    referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let P3 := referenceGaugeNormalThreeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let P := referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let G := referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) p
  have hLower := referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p)
    p lam Lam hUE hsmall hWeak (P3.inverse u)
  have hInv := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u)
      (referenceGaugeNormalThreeHalfMultiplierFamily_inverse_half_inclusion
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  change I (P3.inverse u) = P.inverse (I u) at hInv
  unfold referenceGaugeNormalHighCommutatorFamily referenceGaugeNormalHalfCommutatorFamily
  simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply]
  rw [map_neg,hLower]
  exact congrArg (fun v : SphereSobolev (1/2 : ℝ) => -(G v)) hInv

lemma contDiffAt_referenceGaugeNormalHighCommutatorFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p := by
  have hRoom := hp
  unfold referenceGaugeNormalHighInvertibleLocus at hRoom
  have hJoint := contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)
    hcalc hF hO hD τ0 p p hRoom.1 hRoom.2
  have hDiag : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) => (t,t)) p :=
    contDiffAt_id.prodMk contDiffAt_id
  have hB : ContDiffAt ℝ ∞ (fun t => referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 t) t) p := by
    simpa only [referenceGaugeNormalCoefficientJetsFamily,Function.comp_def] using
      hJoint.comp (f := fun t : ℝ × (R3 × ℝ) => (t,t)) p hDiag
  have hW := (contDiff_referenceGaugeNormalThreeHalfMultiplierFamily_inverse
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt (x := p)
  unfold referenceGaugeNormalHighCommutatorFamily
  exact (hB.clm_comp hW).neg

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHighCommutatorFamily_half_agreement
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceGaugeNormalHighCommutatorFamily
