import Calderon.ActualReferenceWeakRoom
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualNativeTraceGeometryRoom

/-! The original finite inverse and the geometric room, derived before n. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
attribute [local irreducible] referenceStrongDriftFamily referenceRadialEndpointInvertibleLocus
  referenceFramedNormalizedJacobian

lemma exists_reference_commonRadius_finitePhysicalDomain_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) :
    ∃ lam Lam d : ℝ, 0 < lam ∧ 0 < d ∧ d ≤ ρ ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d),
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam ∧
        UnitBallSmallDriftData (fun z => a (p,z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible ∧
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) ∧
        ∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hUE,hSmall⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨lam,Lam,d,hlam,hd,hdρ,?_⟩
  intro p hp
  have hy : ‖p.2.1-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
  have hr : |p.2.2| ≤ d := abs_le.mpr hp.2.2
  have hEll := hUE p ⟨hp.1,hp.2.1,(Icc_subset_Icc (neg_le_neg hdρ) hdρ) hp.2.2⟩
  have hs := hSmall p.1 hp.1 p.2.1 hy p.2.2 hr
  have hLow := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p.1 p.2 lam Lam hEll hs.1
  have hHigh := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 p.1 p.2 lam Lam hEll hs.1
  have hEndpoint := referenceRadialEndpointInvertibleLocus_mem_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p lam Lam hEll hs
  refine ⟨hEll,hs,hEndpoint,⟨hHigh,hLow⟩,?_⟩
  intro x
  have hρ : 0 < ρ := hData.1.2.1
  have hx : x.val ∈ closedBall (0 : R3) 2 :=
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)
      (Metric.sphere_subset_closedBall x.property)
  exact referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
    g L y0 Φ B ε C ρ H a w hData p.1 hp.1 p.2.1 (by linarith) p.2.2
      (by linarith [hr.trans hdρ]) x.val hx

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePhysicalDomain_room
