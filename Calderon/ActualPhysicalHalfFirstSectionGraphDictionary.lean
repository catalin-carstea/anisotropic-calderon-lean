import Calderon.ActualPhysicalHalfFirstSectionGraphConvergence
import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus
  referenceFramedNormalizedJacobian referenceFrameConnectionCoefficient
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint sphereSobolevInclusionL referencePhysicalDensityHalfFromFirstSections
  referencePhysicalDensityOperator referenceDensityCovariantSecondAction

theorem sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (v : R3 → SphereSobolev (3/2:ℝ))
    (η : Fin 3 → R3 → SphereSobolev (3/2:ℝ)) (y : R3)
    (hη : ∀ k : Fin 3, ContDiffAt ℝ ∞ (η k) y)
    (hEq : ∀ k : Fin 3,
      (fun z => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (η k z)) =ᶠ[𝓝 y]
      (fun z => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v z k))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y) =
      referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
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
  have hW : referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • V i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • I (η i y)) := by
    unfold referencePhysicalDensityHalfFromFirstSections
    rfl
  have hLinear : J (referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y) = R y •
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

/-- The finite helper is literally the previously defined uncompressed W. -/
theorem referencePhysicalDensityHalfFromFirstSections_eq_finiteGauge
    {KG KJ : Set (ℝ × (R3 × ℝ))}
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
    (E : ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)
    (g2 : MatrixField) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (v : R3 → SphereSobolev (3/2:ℝ)) (y : R3) :
    referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun j z => referenceFiniteGaugeDensityFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v z j) y =
    referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R v y := by
  unfold referencePhysicalDensityHalfFromFirstSections referenceFiniteGaugePhysicalDensityHalfSection
  rfl

theorem tsupport_referencePhysicalDensityHalfFromFirstSections_subset
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (η : Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (S : Set R3) (hS : IsClosed S) (hSupp : ∀ k, tsupport (η k) ⊆ S) :
    tsupport (fun y => referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y) ⊆ S := by
  classical
  have hFirst (i j : Fin 3) : tsupport (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i) ⊆ S :=
    (tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) i).trans (hSupp j)
  apply closure_minimal ?_ hS
  intro y hy
  by_contra hOutside
  have hEtaZero (k : Fin 3) : η k y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hOutside (hSupp k h))
  have hFirstZero (i j : Fin 3) : referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) z i) (x := y)
      (fun h => hOutside (hFirst i j h))
  apply hy
  simp only [referencePhysicalDensityHalfFromFirstSections,hEtaZero,hFirstZero,
    map_zero,smul_zero,Finset.sum_const_zero,sub_zero,add_zero]

theorem sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections_global
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (v : R3 → SphereSobolev (3/2:ℝ))
    (η : Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (S : Set R3) (hS : IsClosed S)
    (hSuppv : tsupport v ⊆ S) (hSuppη : ∀ k, tsupport (η k) ⊆ S)
    (hη : ∀ k : Fin 3, ContDiff ℝ ∞ (η k))
    (hEq : ∀ k : Fin 3,
      (fun z => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (η k z)) =
      (fun z => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v z k))
    (hGeometry : ∀ y ∈ S,
      (∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible) ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (fun y => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y)) =
    (fun y => referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y) := by
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hHalfSupp := tsupport_referencePhysicalDensityHalfFromFirstSections_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η S hS hSuppη
  have hPSupp := (tsupport_referencePhysicalDensityOperator_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v).trans hSuppv
  funext y
  by_cases hy : y ∈ S
  · exact sphereSobolevInclusionL_referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R v η y
        (fun k => (hη k).contDiffAt) (fun k => (hEq k).eventuallyEq)
          (hGeometry y hy).1 (hGeometry y hy).2
  · have hHalfZero : referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hHalfSupp h))
    have hPZero : referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hPSupp h))
    exact (congrArg J hHalfZero).trans ((map_zero J).trans hPZero.symm)

theorem contDiff_referencePhysicalDensityHalfFromFirstSections_of_support
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (η : Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (hη : ∀ k, ContDiff ℝ ∞ (η k))
    (S : Set R3) (hSupp : ∀ k, tsupport (η k) ⊆ S)
    (hGeometry : ∀ y ∈ S, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible) :
    ContDiff ℝ ∞ (fun y => referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R η y) := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hLow (k : Fin 3) : ContDiff ℝ ∞ (fun y => I (η k y)) := I.contDiff.comp (hη k)
  have hFirst (i j : Fin 3) : ContDiff ℝ ∞ (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i) :=
    contDiff_referenceHighDensityFirstAction_of_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR (η j) (hη j)
        (fun y hy => hGeometry y (hSupp j hy)) i
  have hGam (i k j : Fin 3) : ContDiff ℝ ∞ (fun y => referenceFrameConnectionCoefficient
      g L q y (referenceMetricGramFrame g L (q,y) i) k j) :=
    AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun z => referenceMetricGramFrame g L (q,z) i)
      (contDiff_referenceMetricGramFrame_slice g hg L q i) k j
  have hA (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (contDiff_const.prodMk contDiff_id)
  have hb (i : Fin 3) : ContDiff ℝ ∞
      (fun y => normalizedSecondDriftFrameJoint g g2 L i (q,y)) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (contDiff_const.prodMk contDiff_id)
  unfold referencePhysicalDensityHalfFromFirstSections
  apply ContDiff.smul hR
  apply ContDiff.add
  · apply ContDiff.sum
    intro i hi
    apply ContDiff.sum
    intro j hj
    apply (hA i j).smul
    apply (hFirst i j).sub
    apply ContDiff.sum
    intro k hk
    exact (hGam i k j).smul (hLow k)
  · apply ContDiff.sum
    intro i hi
    exact (hb i).smul (hLow i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
