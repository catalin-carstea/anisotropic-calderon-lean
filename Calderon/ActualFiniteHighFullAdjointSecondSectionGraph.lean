import Calderon.ActualFullAdjointFirstActionCompatibility
import Calderon.ActualFullAdjointFirstActionGerm
import Calderon.ActualFullAdjointFirstActionRegularity
import Calderon.ActualFiniteHighFullAdjointFirstSectionRoom
import Calderon.ActualFiniteHighFullAdjointFirstSectionSupport
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SphereSobolevHalfNegativeInclusionZero

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/
EXPANSION-named-global-reversed-word-graph-v011.md. SAME explicit uncompressed xi. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighFullAdjointFirstAction referenceLowerFullAdjointFirstAction
  referenceFiniteHighFullAdjointFirstSection referenceHighMovingBoundaryActionFamily
  referenceLowerHorizontalAction referenceRadialEndpointInvertibleLocus sphereSobolevInclusionL
  sphereSobolevPartialSumL referenceMetricGramFrame referenceFrameConnectionCoefficient

lemma exists_reference_commonRadius_fullAdjointSecondSection_graph
    (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
      ∀ i j : Fin 3, ∀ y : R3,
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighFullAdjointFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
            (fun z => referenceFiniteHighFullAdjointFirstSection
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u z i) y j) =
        referenceLowerFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun z => referenceHighFullAdjointFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
            (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) z i) y j := by
  obtain ⟨dY,hdY,hdYρ,hYroom⟩ := exists_reference_commonRadius_fullAdjointFirstSection_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨min dY (d/2),lt_min hdY (show 0 < d/2 by positivity),
    (min_le_left _ _).trans hdYρ,?_⟩
  intro n q hq R hR u hu hSupportRoom i j y
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let P : R3 → SphereSobolev (3/2 : ℝ) := fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)
  let eta : R3 → SphereSobolev (3/2 : ℝ) := fun z => referenceFiniteHighFullAdjointFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u z i
  let xi : R3 → SphereSobolev (1/2 : ℝ) := fun z => referenceHighFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta z j
  let innerY : R3 → SphereSobolev (1/2 : ℝ) := fun z => referenceHighFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R P z i
  change J (xi y) = referenceLowerFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R innerY y j
  by_cases hy : y ∈ tsupport u
  · have hs := hSupportRoom y hy
    have hrY : |R y| < dY := hs.2.1.trans_le (min_le_left _ _)
    have hrHalf : |R y| < d/2 := hs.2.1.trans_le (min_le_right _ _)
    have hrD : |R y| ≤ d := by linarith only [hrHalf,hd]
    have hp : (q,(y,R y)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
      refine ⟨hq,?_,abs_le.mp hrD⟩
      simpa only [mem_closedBall,dist_eq_norm] using hs.1.le
    have ha := hRoom (q,(y,R y)) hp
    have hFields :
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible ∧
        (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible ∧
        (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible := by
      simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using ha.2.2.1
    have hEta := hYroom n q hq R hR u hu y hs.1 hrY hs.2.2 i
    have hNear : (fun z => I (eta z)) =ᶠ[𝓝 y] innerY := by
      simpa only [I,eta,P,innerY,referenceHighFullAdjointFirstAction] using hEta.2
    have hCompatible : J (xi y) = referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (fun z => I (eta z)) y j :=
      referenceFullAdjointFirstAction_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j
          ha.2.2.2.2 hFields.2.2 hFields.1 hFields.2.1 eta
          (hEta.1.differentiableAt (by simp))
    exact hCompatible.trans (referenceLowerFullAdjointFirstAction_congr_of_eventuallyEq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => I (eta z)) innerY y j hNear)
  · have hPsupport : tsupport P ⊆ tsupport u := by
      apply closure_minimal ?_ (isClosed_tsupport u)
      intro z hz
      by_contra hzu
      have hU : u z = 0 := image_eq_zero_of_notMem_tsupport hzu
      change sphereSobolevPartialSumL (3/2 : ℝ) n (u z) ≠ 0 at hz
      exact hz (by rw [hU,map_zero])
    have hInnerSupport : tsupport innerY ⊆ tsupport u :=
      (tsupport_referenceHighFullAdjointFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R P i).trans hPsupport
    have hEtaSupport : tsupport eta ⊆ tsupport u :=
      tsupport_referenceFiniteHighFullAdjointFirstSection_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u i
    have hXiSupport : tsupport xi ⊆ tsupport u :=
      (tsupport_referenceHighFullAdjointFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta j).trans hEtaSupport
    have hXi0 : xi y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hXiSupport h))
    have hInnerZero : innerY =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hInnerSupport h))
    have hLowZero := referenceLowerFullAdjointFirstAction_congr_of_eventuallyEq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        innerY (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y j hInnerZero
    have hZeroDerivative : fderiv ℝ (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y = 0 :=
      fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : SphereSobolev (1/2 : ℝ))
    have hZero : referenceLowerFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y j = 0 := by
      simp only [referenceLowerFullAdjointFirstAction,referenceLowerHorizontalAction,
        hZeroDerivative,ContinuousLinearMap.zero_apply,map_zero,zero_add,neg_zero,smul_zero,sub_zero]
    calc
      J (xi y) = 0 := (congrArg J hXi0).trans sphereSobolevInclusionL_half_negative_apply_zero
      _ = referenceLowerFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R innerY y j :=
        (hLowZero.trans hZero).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_fullAdjointSecondSection_graph
