import Calderon.ActualFiniteGaugeDensityFirstSectionSupport
import Calderon.ActualPhysicalDensityOperatorLocality

/-! One literal W; unconditional support. -/
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
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

def referenceFiniteGaugePhysicalDensityHalfSection
    (g2 : MatrixField) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (1/2 : ℝ) :=
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) := fun k z =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u z k
  R y • ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
    (referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient
        g L q y (referenceMetricGramFrame g L (q,y) i) k j • I (η k y))) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • I (η i y))

attribute [local irreducible] referenceFiniteGaugePhysicalDensityHalfSection

theorem tsupport_referenceFiniteGaugePhysicalDensityHalfSection_subset
    (g2 : MatrixField) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) :
    tsupport (fun y => referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u y) ⊆ tsupport u := by
  classical
  let η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) := fun k z =>
    referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u z k
  have hSupport (k : Fin 3) : tsupport (η k) ⊆ tsupport u :=
    tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u k
  have hFirstSupport (i j : Fin 3) : tsupport (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i) ⊆ tsupport u :=
    (tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) i).trans (hSupport j)
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hEtaZero (k : Fin 3) : η k y = 0 :=
    image_eq_zero_of_notMem_tsupport (f := η k) (x := y) (fun h => hOutside (hSupport k h))
  have hFirstZero (i j : Fin 3) : referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) z i) (x := y)
      (fun h => hOutside (hFirstSupport i j h))
  dsimp only [η] at hEtaZero hFirstZero
  apply hy
  simp only [referenceFiniteGaugePhysicalDensityHalfSection, hEtaZero, hFirstZero,
    map_zero, smul_zero, Finset.sum_const_zero, sub_zero, add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugePhysicalDensityHalfSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceFiniteGaugePhysicalDensityHalfSection_subset
