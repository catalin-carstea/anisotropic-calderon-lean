import Calderon.ActualFiniteGaugePhysicalDensityHalfSection
import Calderon.ActualFiniteGaugeDensityFirstSectionGraph
import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-FINITE-GAUGE-PHYSICAL-HALF-SECTION-GRAPH-UPFRONT-v001.md. SAME W, actual derived local eta graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection referenceHighDensityFirstAction
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL sphereSobolevPartialSumL
  referenceFiniteGaugePhysicalDensityHalfSection referencePhysicalDensityOperator
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceFramedNormalizedJacobian
  referenceRadialEndpointInvertibleLocus

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

theorem sphereSobolevInclusionL_referenceFiniteGaugePhysicalDensityHalfSection
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (n : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : ContDiff ℝ ∞ u) (y : R3)
    (hpK : (q,(y,R y)) ∈ KJ) (lam Lam : ℝ)
    (hNear : ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a ((q,(z,R z)),x)) lam Lam ∧
      (∀ x ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(z,R z)),x)‖ ≤ lam/4) ∧
      (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (q,(z,R z)) ∈ G.parameterRoom)
    (hr : R y ≠ 0)
    (hHigh : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceFiniteGaugePhysicalDensityHalfSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u y) =
      referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let v : R3 → SphereSobolev (3/2 : ℝ) := fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)
  let η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) := fun k z =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u z k
  have hη (k : Fin 3) : ContDiffAt ℝ ∞ (η k) y :=
    contDiffAt_referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y k
        hu.contDiffAt hR.contDiffAt hr hHigh
  have hEq (k : Fin 3) : (fun z => I (η k z)) =ᶠ[𝓝 y]
      (fun z => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v z k) :=
    eventually_sphereSobolevInclusionL_referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E hreg hKernel
        n q hq R hR u hu y hpK lam Lam hNear k
  let V : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) := fun i j =>
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient
        g L q y (referenceMetricGramFrame g L (q,y) i) k j • I (η k y)
  have hSecond (i j : Fin 3) : J (V i j) = referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i j :=
    referenceDensityCovariantSecondAction_half_graph_of_local_high_firstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R v η y i j hη hEq hInv hWeak
  have hFirst (i : Fin 3) : J (I (η i y)) = J
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i) :=
    congrArg J (hEq i).self_of_nhds
  have hW : referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u y = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • V i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • I (η i y)) := by
    unfold referenceFiniteGaugePhysicalDensityHalfSection
    rfl
  have hLinear : J (referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u y) = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • J (V i j)) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J (I (η i y))) := by
    exact (congrArg J hW).trans (by simp only [map_smul,map_add,map_sum])
  have hTransport : R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • J (V i j)) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J (I (η i y))) = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i)) :=
    congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z)
      (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t)
        (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
          congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
            referenceDensityPrincipalFrameCoefficient g g2 L q y i j • z) (hSecond i j))))
        (Finset.sum_congr rfl (fun i _ => congrArg
          (fun z : SphereSobolev (-(1/2 : ℝ)) => normalizedSecondDriftFrameJoint g g2 L i (q,y) • z) (hFirst i))))
  have hLiteral : referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i)) := by
    unfold referencePhysicalDensityOperator
    rfl
  exact hLinear.trans (hTransport.trans hLiteral.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteGaugePhysicalDensityHalfSection
