import Calderon.ActualSameRoomFixedDensityGraph
import Calderon.ActualFiniteGaugeDensitySecondSectionGlobalGraph

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral

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
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

private lemma physicalGeometryRoom (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d),
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
          g L Φ (p.1,(p.2,x.val))).IsInvertible := by
  obtain ⟨lam,Lam,d,hlam,hd,hdrho,hRoom⟩ :=
    exists_reference_commonRadius_finitePhysicalDomain_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d,hd,hdrho,?_⟩
  intro p hp
  exact ⟨(hRoom p hp).2.2.1,(hRoom p hp).2.2.2.2⟩

private lemma weakInverse_of_endpointRoom (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible := by
  unfold referenceRadialEndpointInvertibleLocus at hp
  exact hp.2.1

/- The exact old quantified bundle is packaged as data only after its existing
existence theorem is proved. This introduces no mathematical premise. -/
private structure OldFiniteGraphRoom (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace) where
  dX : ℝ
  pos_dX : 0 < dX
  le_rho : dX ≤ ρ
  G : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX))
  E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData)
    (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX))
  dOld : ℝ
  pos_dOld : 0 < dOld
  le_dX : dOld ≤ dX
  oldGraph : oldFiniteSectionProperty g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dX dOld G E

private def oldFiniteGraphRoomOfData
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    OldFiniteGraphRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 := by
  classical
  apply Classical.choice
  obtain ⟨dX,hdX,hdXrho,G,E,dOld,hdOld,hdOldX,hOld⟩ :=
    exists_reference_commonRadius_finiteGaugeDensitySecondSection_globalGraph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  exact ⟨{
    dX := dX
    pos_dX := hdX
    le_rho := hdXrho
    G := G
    E := E
    dOld := dOld
    pos_dOld := hdOld
    le_dX := hdOldX
    oldGraph := hOld }⟩

attribute [local irreducible] oldFiniteGraphRoomOfData

theorem exists_reference_commonRadius_same_finiteDensityGraph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ dX : ℝ, 0 < dX ∧ dX ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
          (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
      ∃ E : ReferenceJacobiCompactExtensionRoom
          (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData)
          (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dX) dX)),
      ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ dX ∧
      ∀ (q : ℝ), q ∈ Icc (0:ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (5/2:ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
      ∀ j : Fin 3,
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
  let W := oldFiniteGraphRoomOfData
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  let dX := W.dX
  have hdX : 0 < dX := W.pos_dX
  have hdXrho : dX ≤ ρ := W.le_rho
  let G := W.G
  let E := W.E
  let dOld := W.dOld
  have hdOld : 0 < dOld := W.pos_dOld
  have hdOldX : dOld ≤ dX := W.le_dX
  have hOld := W.oldGraph
  obtain ⟨dPhys,hdPhys,hdPhysrho,hPhys⟩ :=
    physicalGeometryRoom g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let d0 := min dOld (dPhys/2)
  have hd0 : 0 < d0 := lt_min hdOld (by positivity)
  have hd0Old : d0 ≤ dOld := min_le_left _ _
  have hd0X : d0 ≤ dX := hd0Old.trans hdOldX
  have hd0Phys : d0 ≤ dPhys := (min_le_right _ _).trans (by linarith)
  refine ⟨dX,hdX,hdXrho,G,E,d0,hd0,hd0X,?_⟩
  exact sameFiniteDensityGraph_in_fixed_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      dX dOld dPhys d0 G E hreg hd0Old hd0X hd0Phys hOld hPhys

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
