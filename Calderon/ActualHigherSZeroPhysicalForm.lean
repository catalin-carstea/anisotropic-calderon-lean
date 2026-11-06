import Calderon.ActualHigherSZeroPhysicalCommutatorGraph
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalForm
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorNativeForm ActualHigherSZeroScalarNativeForm
  ActualHigherSZeroPhysicalCommutatorGraph
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BETA" => actualReferenceBeta g L
local notation "PC" => nativeZeroPhysicalCommutatorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GP" => nativeZeroPhysicalCommutatorOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NC" => nativeScalarZeroCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] ActualHigherSZeroPhysicalCommutatorGraph.nativeZeroPhysicalCommutatorHalf
  ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient coreCoordinateSecondAction actualPrincipalMatrix

/-- Actual principal coefficients in the full Half-valued physical zero-S commutator. -/
def nativeScalarZeroPhysicalCommutatorHalf
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  PC hreg δ0 W g2 δr Ar p hδr hAr q
    (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
    (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh) F x
local notation "AC" => nativeScalarZeroPhysicalCommutatorHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Full physical output of that exact Half commutator. -/
def nativeScalarZeroPhysicalCommutatorOut
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (AC hreg δ0 W g2 δr Ar p hδr hAr q h hh F x)
local notation "PO" => nativeScalarZeroPhysicalCommutatorOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] nativeScalarZeroPhysicalCommutatorHalf

/-- Original physical reference-form task, with explicit existing positivity/smoothness proofs. -/
def ActualScalarZeroPhysicalFormBound
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
    ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    ∀ hh : (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)),
    ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ tsupport F.val, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ tsupport F.val, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ tsupport F.val, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F.val x,PO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        ⟪F.val x,PO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x
local notation "PhysicalForm" => ActualScalarZeroPhysicalFormBound
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem exists_actual_scalar_zero_physical_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    PhysicalForm hreg δ0 W δ g2 := by
  obtain ⟨K,hK,hcap⟩ := exists_actual_scalar_zero_commutator_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  refine ⟨K,hK,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  have hn := hcap δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hglo := nativeZeroPhysicalCommutator_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq aa ha F hTF
  have hActualGraph (y : R3) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (AC hreg δ0 W g2 δr Ar p hδr hAr q h hh F y) = NC g2 δr Ar p q h F y := by
    unfold nativeScalarZeroPhysicalCommutatorHalf
    exact congrFun hglo y
  have hp (x : R3) : sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F x)
      (NC g2 δr Ar p q h F x) = ⟪F.val x,PO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ :=
    ActualHigherSPhysicalPairing.physical_pairing_of_graph hO hD F
      (AC hreg δ0 W g2 δr Ar p hδr hAr q h hh F) (NC g2 δr Ar p q h F)
      hActualGraph x
  have he : (fun x => referenceDensityFamily g L (q,x)*sphereSobolevDualPairing (1/2 : ℝ)
      (halfInput hO hD F x) (NC g2 δr Ar p q h F x)) =
      (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,PO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) := by
    funext x
    rw [hp x]
  have hpi : Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,PO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) := he ▸ hn.1
  have hi := congrArg (fun J : R3 → ℝ => ∫ x, J x) he
  refine ⟨hpi,hn.2.1,?_⟩
  calc
    _ = |∫ x, referenceDensityFamily g L (q,x)*sphereSobolevDualPairing (1/2 : ℝ)
        (halfInput hO hD F x) (NC g2 δr Ar p q h F x)| := (congrArg abs hi).symm
    _ ≤ _ := hn.2.2

/-- The same common room/Jacobian guard before g2 and every actual profile/input. -/
theorem exists_retained_actual_scalar_zero_physical_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → PhysicalForm hreg δ0 W δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_zero_physical_reference_form g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalForm
