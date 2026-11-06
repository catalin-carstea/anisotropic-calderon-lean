import Calderon.ActualFiniteFirstSectionGraphLimits
import Calderon.ActualFiniteGaugeDensitySecondSectionGlobalGraph

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral NativeThreeHalfCoefficientMultiplier SmoothMetricFrame

attribute [local irreducible] referenceRadialEndpointInvertibleLocus referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceFiveHalfDensityFirstActionInRoom
  referenceFiniteGaugeDensityFirstSection referenceHighDensityFirstAction referenceLowerDensityFirstAction
  sphereSobolevInclusionL sphereSobolevPartialSumL referenceStrongDriftFamily
  referenceFramedNormalizedJacobian
  referenceWeakDirichletEnergyFamily referenceFiveHalfAdjointJacobiBoundaryInRoom
  referenceFiveHalfAdjointMovingBoundaryInRoom referenceFiveHalfHorizontalAngularL referenceMetricGramFrame

private lemma weakInverse_of_endpointRoom (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible := by
  unfold referenceRadialEndpointInvertibleLocus at hp
  exact hp.2.1

def oldFiniteSectionProperty
    (dX d0 : ℝ)
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)))
    (E : ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData)
      (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX))) : Prop :=
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
                        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f x j) y i

theorem sameFiniteDensityGraph_in_fixed_room
    (dX dOld dPhys d0 : ℝ)
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)))
    (E : ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData)
      (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)))
    (hreg : FixedDirichletRegularity)
    (hd0Old : d0 ≤ dOld) (hd0X : d0 ≤ dX) (hd0Phys : d0 ≤ dPhys)
    (hOld : oldFiniteSectionProperty g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dX dOld G E)
    (hPhys : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dPhys) dPhys),
      p ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hSupport : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0)
    (j : Fin 3) :
        let v : R3 → SphereSobolev (3/2:ℝ) := fun y =>
          sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
        let eta : ℕ → R3 → SphereSobolev (3/2:ℝ) := fun n y => referenceFiniteGaugeDensityFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y j
        let etaInf : R3 → SphereSobolev (3/2:ℝ) := fun y => referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u y j
        ContDiff ℝ ∞ etaInf ∧ HasCompactSupport etaInf ∧
        (∀ n : ℕ, ContDiff ℝ ∞ (eta n) ∧ HasCompactSupport (eta n) ∧
          (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (eta n y)) =
            (fun y => referenceHighDensityFirstAction
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
                (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y j) ∧
          ∀ (i : Fin 3) (y : R3),
            sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
              (referenceHighDensityFirstAction
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (eta n) y i) =
            referenceLowerDensityFirstAction
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
                (fun z => referenceHighDensityFirstAction
                  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
                    (fun z' => sphereSobolevPartialSumL (3/2:ℝ) n (v z')) z j) y i) ∧
        (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (etaInf y)) =
          (fun y => referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y j) ∧
        (∀ n : ℕ, eta n = fun y => referenceFiveHalfDensityFirstActionInRoom
          g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
            (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y j) ∧
        Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖eta n y - etaInf y‖^2)
          atTop (𝓝 0) ∧
        (∀ X : R3, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
          ‖fderiv ℝ (eta n) y X - fderiv ℝ etaInf y X‖^2) atTop (𝓝 0)) ∧
        (∀ n : ℕ, tsupport (eta n) ⊆ tsupport u) ∧ tsupport etaInf ⊆ tsupport u ∧
        (∀ y ∈ tsupport u, R y ≠ 0 ∧
          (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
            g L Φ (q,((y,R y),x.val))).IsInvertible) := by
  extract_lets v eta etaInf
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  have hv : ContDiff ℝ ∞ v := Iin.contDiff.comp hu
  have hvc : HasCompactSupport v := hc.comp_left (map_zero Iin)
  have hvSupp : tsupport v ⊆ tsupport u := tsupport_comp_subset (map_zero Iin) u
  have hvRoom : ∀ y ∈ tsupport v, ‖y-y0‖ < ρ ∧ |R y| < dOld ∧ R y ≠ 0 := by
    intro y hy
    have hAt := hSupport y (hvSupp hy)
    exact ⟨hAt.1,hAt.2.1.trans_le hd0Old,hAt.2.2⟩
  have hOldAt (n : ℕ) := hOld n q hq R hR v hv hvc hvRoom j
  have hTubeX (y : R3) (hy : y ∈ tsupport u) :
      (q,(y,R y)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX) := by
    refine ⟨hq,?_,abs_le.mp ((hSupport y hy).2.1.le.trans hd0X)⟩
    simpa only [mem_closedBall,dist_eq_norm] using (hSupport y hy).1.le
  have hTubePhys (y : R3) (hy : y ∈ tsupport u) :
      (q,(y,R y)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dPhys) dPhys) := by
    refine ⟨hq,?_,abs_le.mp ((hSupport y hy).2.1.le.trans hd0Phys)⟩
    simpa only [mem_closedBall,dist_eq_norm] using (hSupport y hy).1.le
  have hEndpoint (y : R3) (hy : y ∈ tsupport u) :
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (hPhys (q,(y,R y)) (hTubePhys y hy)).1
  have hCommon : ∀ y ∈ tsupport u,
      (q,(y,R y)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX) ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible :=
    fun y hy => ⟨hTubeX y hy,weakInverse_of_endpointRoom
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) (hEndpoint y hy)⟩
  have hRegular : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun y hy => ⟨(hSupport y hy).2.2,hEndpoint y hy⟩
  have hNew := referenceFiniteGaugeDensityFirstSection_graphLimits_of_same_source
    g L y0 Φ B ε C ρ H a w hData hg E G hcalc hF hO hD τ0 hreg q R u hu hc hR j
      (fun n => (hOldAt n).2.2.1) hCommon hRegular
  have hLower := referenceDensityFirstActionInRoom_global_compatibility_of_support
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R u hu j hCommon
  constructor
  · exact hNew.1
  constructor
  · exact hNew.2.1
  constructor
  · intro n
    exact hOldAt n
  constructor
  · exact hLower
  constructor
  · exact hNew.2.2.1
  constructor
  · exact hNew.2.2.2.1
  constructor
  · exact hNew.2.2.2.2
  constructor
  · intro n
    exact (tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v j).trans hvSupp
  constructor
  · exact tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R u j
  · intro y hy
    exact ⟨(hSupport y hy).2.2,hEndpoint y hy,
      (hPhys (q,(y,R y)) (hTubePhys y hy)).2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
