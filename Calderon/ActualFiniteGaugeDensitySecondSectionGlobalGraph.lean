import Calderon.ActualFiniteGaugeDensityFirstSectionGlobalGraph
import Calderon.ActualFiniteGaugeDensityFirstSectionSupport
import Calderon.ActualCovariantDensityFirstActions
import Calderon.ActualPhysicalDensityOperatorLocality
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.ActualReferenceWeakHalfLift
import Calderon.SphereSobolevHalfNegativeInclusionZero

/-! Full AUTHOR upfront034, actual-Y-second-action-domain-author-oct16-v001.
The SAME G/E on the larger original tube; actual uncompressed second-word graph. -/
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

attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceFiniteGaugeDensityFirstSection sphereSobolevInclusionL sphereSobolevPartialSumL
  referenceRadialEndpointInvertibleLocus referenceMetricGramFrame

theorem exists_reference_commonRadius_finiteGaugeDensitySecondSection_globalGraph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ dX : ℝ, 0 < dX ∧ dX ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
        ∃ E : ReferenceJacobiCompactExtensionRoom
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData)
            (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
          ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ dX ∧
            ∀ (N : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
              ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
              ∀ (v : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ v → HasCompactSupport v →
              (∀ y ∈ tsupport v, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) → ∀ j : Fin 3,
                let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
                let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
                let f : R3 → SphereSobolev (3/2 : ℝ) :=
                  fun y => sphereSobolevPartialSumL (3/2 : ℝ) N (v y)
                let eta : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteGaugeDensityFirstSection
                  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E N q R v y j
                ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
                  (fun y => I (eta y)) = (fun y => referenceHighDensityFirstAction
                    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f y j) ∧
                  ∀ i : Fin 3, ∀ y : R3,
                    J (referenceHighDensityFirstAction
                      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta y i) =
                    referenceLowerDensityFirstAction
                      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
                      (fun x => referenceHighDensityFirstAction
                        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f x j) y i := by
  obtain ⟨dX,hdX,hdXρ,G,E,hXbundle⟩ := exists_reference_commonRadius_finiteGaugeDensityFirstSection_globalGraph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨dX,hdX,hdXρ,G,E,min dX (d/2),lt_min hdX (by positivity),min_le_left _ _,?_⟩
  intro N q hq R hR v hv hcv hvRoom j
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Xh : (R3 → SphereSobolev (3/2 : ℝ)) → R3 → Fin 3 → SphereSobolev (1/2 : ℝ) :=
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
  let Xl : (R3 → SphereSobolev (1/2 : ℝ)) → R3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
  let f : R3 → SphereSobolev (3/2 : ℝ) := fun y => sphereSobolevPartialSumL (3/2 : ℝ) N (v y)
  let eta : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteGaugeDensityFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E N q R v y j
  have hvRoomX : ∀ y ∈ tsupport v, ‖y-y0‖ < ρ ∧ |R y| < dX ∧ R y ≠ 0 := by
    intro y hy
    have hs := hvRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_left _ _),hs.2.2⟩
  have hXB : ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
      (fun y => I (eta y)) = (fun y => Xh f y j) :=
    hXbundle N q hq R hR v hv hcv hvRoomX j
  have hEtaSupport : tsupport eta ⊆ tsupport v :=
    tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E N q R v j
  have hfSupport : tsupport f ⊆ tsupport v :=
    tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2 : ℝ) N)) v
  refine ⟨hXB.1,hXB.2.1,hXB.2.2,?_⟩
  intro i y
  by_cases hy : y ∈ tsupport v
  · have hs := hvRoom y hy
    have hrHalf : |R y| < d/2 := hs.2.1.trans_le (min_le_right _ _)
    have hr : |R y| ≤ d := by linarith only [hrHalf,hd]
    have hp : (q,(y,R y)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
      refine ⟨hq,?_,abs_le.mp hr⟩
      simpa only [mem_closedBall,dist_eq_norm] using hs.1.le
    have ha := hRoom (q,(y,R y)) hp
    have hWeak : (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible :=
      isInvertible_referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y)) lam ha.2.1
    have hCompat := referenceDensityFirstAction_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i
      ha.2.2.2.2 hWeak eta (hXB.1.differentiable (by simp) y)
    exact hCompat.trans (congrArg (fun V : R3 → SphereSobolev (1/2 : ℝ) => Xl V y i) hXB.2.2)
  · have hHighSupport : tsupport (fun x => Xh eta x i) ⊆ tsupport v :=
      (tsupport_referenceHighDensityFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta i).trans hEtaSupport
    have hFirstSupport : tsupport (fun x => Xh f x j) ⊆ tsupport v :=
      (tsupport_referenceHighDensityFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f j).trans hfSupport
    have hLowSupport : tsupport (fun x => Xl (fun z => Xh f z j) x i) ⊆ tsupport v :=
      (tsupport_referenceLowerDensityFirstAction_subset
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => Xh f z j) i).trans hFirstSupport
    have hHigh0 : Xh eta y i = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun x : R3 => Xh eta x i) (x := y) (fun h => hy (hHighSupport h))
    have hLow0 : Xl (fun z => Xh f z j) y i = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun x : R3 => Xl (fun z => Xh f z j) x i) (x := y)
        (fun h => hy (hLowSupport h))
    exact ((congrArg J hHigh0).trans sphereSobolevInclusionL_half_negative_apply_zero).trans hLow0.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteGaugeDensitySecondSection_globalGraph
