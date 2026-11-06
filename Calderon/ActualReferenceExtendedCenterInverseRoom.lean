import Calderon.WeightedCommonSupportCoefficients
import Calderon.MixedLinearDriftBounds
import Calderon.CompactParameterReferenceWeakDriftCoercivity
import Calderon.ActualReferenceStrongRoom
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceGaugeNormalHighCommutatorDefinition

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator

/-- A fresh uniform inverse room on the larger centre compact, for the original data. -/
theorem exists_reference_commonRadius_extended_center_inverse_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ lam Lam d0 : ℝ, 0 < lam ∧ 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ p : ℝ × (R3 × ℝ), p.1 ∈ Icc (0 : ℝ) 1 →
        p.2.1 ∈ closedBall y0 (3*ρ/2) → |p.2.2| ≤ d0 →
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
          (fun z => a (p,z)) lam Lam ∧
        UnitBallSmallDriftData (fun z => a (p,z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        p ∈ referenceGaugeNormalHighInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc := by
  classical
  -- E1.1: retain the supplied data and use its exact global extension fields.
  have hSaved := hData
  rcases hSaved with
    ⟨hPositive, _hBase, _hDrift, hBeta, _hAIdentity, _hBetaValue,
      _hBetaSupport, hZero, _hJets, _hJetsNormalized, _hMetric,
      _hMixedD, _hMixedBeta, _hFullBounds⟩
  rcases hPositive with
    ⟨_hNormal, hρ, _hρε, _hHDef, haDef, _hwDef, hH, hPos, ha, _hw,
      _hSupport, _hLocal, _hZeroJet, _hOldUE, _hOldMixed⟩
  -- E1.2: fresh compact ellipticity on the SAME larger-center data.
  let Qc : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 (3*ρ/2)
  let Qp : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (3*ρ/2) ×ˢ Icc (-ρ) ρ)
  have hQp : IsCompact Qp :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  obtain ⟨lam, Lam, hCutoffUE⟩ :=
    exists_uniformlyElliptic_cutoffPrincipalCoefficient H hH hPos Qp hQp
  have hUEClosed : ∀ p ∈ Qp,
      TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
        (fun z => a (p,z)) lam Lam := by
    intro p hp
    simpa only [haDef] using hCutoffUE p hp
  have hBaseParam : (0,(y0,(0 : ℝ))) ∈ Qp :=
    ⟨⟨le_rfl, by norm_num⟩, mem_closedBall_self (by positivity),
      ⟨by linarith, hρ.le⟩⟩
  have hlam : 0 < lam := (hUEClosed (0,(y0,0)) hBaseParam).1
  have hUE : ∀ p ∈ Qp,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => a (p,z)) lam Lam := by
    intro p hp
    refine ⟨(hUEClosed p hp).1, (hUEClosed p hp).2.1, ?_⟩
    intro z hz
    exact (hUEClosed p hp).2.2
      (by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz)
  -- E1.3: global zero-slice drift gives a fresh uniform linear radial bound.
  let F : (ℝ × (R3 × R3)) × ℝ → R3 :=
    referenceCoefficientRadialReorder
      (conformalReferenceWeightedFramedDrift g L Φ H w)
  have hFReorder : ContDiff ℝ ∞ F :=
    contDiff_referenceCoefficientRadialReorder _ hBeta
  let Qz : Set (ℝ × (R3 × R3)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (3*ρ/2) ×ˢ closedBall (0 : R3) 2)
  have hQz : IsCompact Qz :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hFZero (u : ℝ × (R3 × R3)) : F (u,0) = 0 :=
    (hZero u.1 u.2.1 u.2.2).2
  obtain ⟨D, hDNonneg, hMixed⟩ :=
    compactMixedLinearBounds_of_zero_slice F hFReorder Qz hQz hFZero ρ hρ.le 0
  have hLinear (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
      (y : R3) (hy : y ∈ closedBall y0 (3*ρ/2))
      (r : ℝ) (hr : |r| ≤ ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ D*|r| := by
    have h := (hMixed 0 (by norm_num) (q,(y,z)) ⟨hq,hy,hz⟩ r hr).1
    rw [parameterJetField_eq_iteratedFDeriv 0 F hFReorder, norm_iteratedFDeriv_zero] at h
    exact h
  -- E1.4: choose the weak radius BEFORE every coefficient parameter and order.
  let A : ((ℝ × R3) × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
    jointReferenceRadialReorder a
  let beta : ((ℝ × R3) × ℝ) × R3 → R3 :=
    jointReferenceRadialReorder (conformalReferenceWeightedFramedDrift g L Φ H w)
  have hA : ContDiff ℝ ∞ A := contDiff_jointReferenceRadialReorder a ha
  have hbeta : ContDiff ℝ ∞ beta :=
    contDiff_jointReferenceRadialReorder _ hBeta
  have hUEQ : ∀ p ∈ Qc ×ˢ Icc (-ρ) ρ,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => A (p,z)) lam Lam := by
    intro p hp
    exact hUE (p.1.1,(p.1.2,p.2)) ⟨hp.1.1,hp.1.2,hp.2⟩
  have hBound : ∀ p ∈ Qc ×ˢ Icc (-ρ) ρ, ∀ z ∈ (ballOpens : Set R3),
      ‖beta (p,z)‖ ≤ D*|p.2| := by
    intro p hp z hz
    have hz1 : z ∈ closedBall (0 : R3) 1 :=
      by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz
    have hz2 : z ∈ closedBall (0 : R3) 2 :=
      closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz1
    exact hLinear p.1.1 hp.1.1 p.1.2 hp.1.2 p.2 (abs_le.mpr hp.2) z hz2
  obtain ⟨d0, hd0, hd0ρ, hSmall⟩ :=
    exists_uniform_smallRadius_parameter_drift_coercivity
      A hA beta hbeta Qc ρ lam Lam D hρ hlam hDNonneg hUEQ hBound
  have hRoom (p : ℝ × (R3 × ℝ))
      (hq : p.1 ∈ Icc (0 : ℝ) 1)
      (hy : p.2.1 ∈ closedBall y0 (3*ρ/2)) (hr : |p.2.2| ≤ d0) :
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => a (p,z)) lam Lam ∧
      UnitBallSmallDriftData (fun z => a (p,z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
      p ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      p ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc := by
    have hpρ : p ∈ Qp := ⟨hq,hy,abs_le.mp (hr.trans hd0ρ)⟩
    have hUEp : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => a (p,z)) lam Lam := hUE p hpρ
    have hpSmall : ((p.1,p.2.1),p.2.2) ∈ Qc ×ˢ Icc (-d0) d0 :=
      ⟨⟨hq,hy⟩,abs_le.mp hr⟩
    have hs : UnitBallSmallDriftData (fun z => a (p,z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam :=
      hSmall ((p.1,p.2.1),p.2.2) hpSmall
    have hStrong (s : ℕ) :
        (referenceStrongDriftFamily
          g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).IsInvertible :=
      referenceStrongDriftFamily_isInvertible_of_smallDrift
        g L y0 Φ B ε C ρ H a w hData hcalc hreg s p.1 p.2 lam Lam hUEp hs.1
    have hRadial : p ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      referenceRadialEndpointInvertibleLocus_mem_of_smallDrift
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p lam Lam hUEp hs
    exact ⟨hUEp,hs,hRadial,⟨hStrong 1,hStrong 0⟩⟩
  exact ⟨lam,Lam,d0,hlam,hd0,hd0ρ,hRoom⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
