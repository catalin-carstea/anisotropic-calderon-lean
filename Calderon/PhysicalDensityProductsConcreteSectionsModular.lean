import Calderon.PhysicalDensityProductsOperatorSmoothness
import Calderon.SupportedOperatorSection
import Calderon.SphereSobolevHalfToL2

/-! DATA-only concrete four-property section obligations. Upfront expansion:
ProductsConcreteSupportedSections.EXPANSION.DATA.md. No check claimed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

set_option Elab.async false

theorem tsupport_referencePhysicalDensityProducts_finiteCore_section
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    tsupport pF ⊆ tsupport F.val := by
  classical
  intro pF
  have hu : tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) ⊆ tsupport F.val :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.1
  apply closure_minimal ?_ (isClosed_tsupport F.val)
  intro y hy
  by_contra hn
  have hn' : y ∉ tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) :=
    fun h => hn (hu h)
  have hz : finiteCoreSobolevLift hO hD (3/2 : ℝ) F y = 0 :=
    image_eq_zero_of_notMem_tsupport hn'
  exact hy (by simp only [pF,hz,map_zero])

theorem contDiff_referencePhysicalDensityProducts_finiteCore_section
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (_hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    ContDiff ℝ ∞ pF := by
  classical
  intro pF
  let uF : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let Op : R3 → Hi →L[ℝ] Half := fun y => referencePhysicalDensityProductsHalfOperator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let U : Set R3 := {y | R y ≠ 0 ∧
    (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
  have hNatural := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hOperators := contDiffOn_referencePhysicalDensityProducts_half_operators
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2 q hq R hR
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hSection := contDiff_comp_clm_apply_of_tsupport_subset
    U hNatural.1 uF hRep.1 hRep.2.1
    (fun y hy => hRoom y (hFs (hRep.2.2.1 hy)))
    Op hOperators.1 (sphereSobolevHalfToL2L hO hD)
  exact hSection.1

theorem referencePhysicalDensityProducts_finiteCore_section_properties
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (_hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    ContDiff ℝ ∞ pF ∧ HasCompactSupport pF ∧ MemLp pF 2 (volume : Measure R3) ∧
      tsupport pF ⊆ tsupport F.val := by
  classical
  intro pF
  have hs : tsupport pF ⊆ tsupport F.val :=
    tsupport_referencePhysicalDensityProducts_finiteCore_section
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R F
  have hd : ContDiff ℝ ∞ pF :=
    contDiff_referencePhysicalDensityProducts_finiteCore_section
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2
      q hq R hR K _hKgeom hRoom F hFs
  have hc : HasCompactSupport pF :=
    F.property.2.1.of_isClosed_subset (isClosed_tsupport pF) hs
  exact ⟨hd,hc,hd.continuous.memLp_of_hasCompactSupport hc,hs⟩

theorem tsupport_referencePhysicalDensityProductsAdjoint_finiteCore_section
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsAdjointHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    tsupport pF ⊆ tsupport F.val := by
  classical
  intro pF
  have hu : tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) ⊆ tsupport F.val :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.1
  apply closure_minimal ?_ (isClosed_tsupport F.val)
  intro y hy
  by_contra hn
  have hn' : y ∉ tsupport (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) :=
    fun h => hn (hu h)
  have hz : finiteCoreSobolevLift hO hD (3/2 : ℝ) F y = 0 :=
    image_eq_zero_of_notMem_tsupport hn'
  exact hy (by simp only [pF,hz,map_zero])

theorem contDiff_referencePhysicalDensityProductsAdjoint_finiteCore_section
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (_hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsAdjointHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    ContDiff ℝ ∞ pF := by
  classical
  intro pF
  let uF : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let Op : R3 → Hi →L[ℝ] Half := fun y => referencePhysicalDensityProductsAdjointHalfOperator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let U : Set R3 := {y | R y ≠ 0 ∧
    (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
  have hNatural := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hOperators := contDiffOn_referencePhysicalDensityProducts_half_operators
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2 q hq R hR
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hSection := contDiff_comp_clm_apply_of_tsupport_subset
    U hNatural.1 uF hRep.1 hRep.2.1
    (fun y hy => hRoom y (hFs (hRep.2.2.1 hy)))
    Op hOperators.2 (sphereSobolevHalfToL2L hO hD)
  exact hSection.1

theorem referencePhysicalDensityProductsAdjoint_finiteCore_section_properties
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (_hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) :
    let pF : R3 → SphereL2 := fun y => sphereSobolevHalfToL2L hO hD
      (referencePhysicalDensityProductsAdjointHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))
    ContDiff ℝ ∞ pF ∧ HasCompactSupport pF ∧ MemLp pF 2 (volume : Measure R3) ∧
      tsupport pF ⊆ tsupport F.val := by
  classical
  intro pF
  have hs : tsupport pF ⊆ tsupport F.val :=
    tsupport_referencePhysicalDensityProductsAdjoint_finiteCore_section
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R F
  have hd : ContDiff ℝ ∞ pF :=
    contDiff_referencePhysicalDensityProductsAdjoint_finiteCore_section
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2
      q hq R hR K _hKgeom hRoom F hFs
  have hc : HasCompactSupport pF :=
    F.property.2.1.of_isClosed_subset (isClosed_tsupport pF) hs
  exact ⟨hd,hc,hd.continuous.memLp_of_hasCompactSupport hc,hs⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
