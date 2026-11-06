import Calderon.ActualHigherSZeroPhysicalGraph
import Calderon.FiniteCoreCoordinateSecondAction
import Calderon.ActualHigherSZeroScalarNativeForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalCommutatorGraph
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualHigherSScalarCommutatorNativeForm ActualHigherSFirstPhysicalCommutatorGraph
  ActualHigherSZeroScalarCommutatorForm ActualHigherSZeroPhysicalGraph
section Algebra
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
/-- The literal nine zero-coordinate commutators are the exact difference of the two actions. -/
lemma scalar_zero_coordinate_sum_eq_actions (a : Fin 3 → Fin 3 → R3 → ℝ)
    (Z : R3 → (E →L[ℝ] N)) (u : R3 → E) (x : R3) :
    scalarZeroCoordinateCommutatorSum a Z u x =
      Z x (coordinateSecondAction a u x)-coordinateSecondAction a (fun y => Z y (u y)) x := by
  simp only [scalarZeroCoordinateCommutatorSum,scalarZeroCoordinateCommutator,
    coordinateSecondAction,Finset.sum_sub_distrib,map_sum]
end Algebra
attribute [local irreducible] ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  ActualHigherSZeroPhysicalGraph.nativeZeroHalf coreCoordinateSecondAction
  coordinateSecondAction scalarZeroCoordinateCommutatorSum sphereSobolevInclusionL

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
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
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Genuine Half commutator on the transformed finite input and the full zero Half field. -/
def nativeZeroPhysicalCommutatorHalf
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ZH hreg δ0 W g2 δr Ar p hδr hAr q (coreCoordinateSecondAction hO hD aa ha F) x -
    coordinateSecondAction aa (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) x
local notation "PC" => nativeZeroPhysicalCommutatorHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact global negative graph, differentiating only the global supported field equality. -/
theorem nativeZeroPhysicalCommutator_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (fun x => JL (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F x)) =
      scalarZeroCoordinateCommutatorSum aa (fun y => CZc g2 δr Ar p q y) (UF F) := by
  let FA := coreCoordinateSecondAction hO hD aa ha F
  have hsub : tsupport FA.val ⊆ tsupport F.val := coreCoordinateSecondAction_tsupport hO hD aa ha F
  have hTA : ∀ x ∈ tsupport FA.val, (Tq δr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x (hsub hx)
  have hUA : UF FA = coordinateSecondAction aa (UF F) :=
    finiteCoreSobolevLift_coreCoordinateSecondAction hO hD (3/2 : ℝ) aa ha F
  have hZF : (fun x => JL (ZH hreg δ0 W g2 δr Ar p hδr hAr q F x)) =
      fun x => CZc g2 δr Ar p q x (UF F x) :=
    funext (fun x => nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF x)
  have hrF := nativeZeroHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hA := coordinateSecondAction_transfer JL aa (ZH hreg δ0 W g2 δr Ar p hδr hAr q F) hrF.1
  funext x
  have hLeft := nativeZeroHalf_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq FA hTA x
  have hLeft' := hLeft.trans (congrArg (CZc g2 δr Ar p q x) (congrFun hUA x))
  dsimp only [FA] at hLeft'
  have hRight := (congrFun hA x).trans
    (congrArg (fun v : R3 → Neg => coordinateSecondAction aa v x) hZF)
  unfold nativeZeroPhysicalCommutatorHalf
  rw [map_sub]
  exact (congrArg₂ (fun u v : Neg => u-v) hLeft' hRight).trans
    (scalar_zero_coordinate_sum_eq_actions aa (fun y => CZc g2 δr Ar p q y) (UF F) x).symm

/-- Genuine smooth compact Half field, with support in the original finite input support. -/
theorem nativeZeroPhysicalCommutator_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ∧
      tsupport (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ⊆ tsupport F.val ∧
      HasCompactSupport (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) := by
  let FA := coreCoordinateSecondAction hO hD aa ha F
  have hsub : tsupport FA.val ⊆ tsupport F.val := coreCoordinateSecondAction_tsupport hO hD aa ha F
  have hTA : ∀ x ∈ tsupport FA.val, (Tq δr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x (hsub hx)
  have hrA := nativeZeroHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq FA hTA
  have hrF := nativeZeroHalf_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hs : ContDiff ℝ ∞ (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) :=
    hrA.1.sub (contDiff_coordinateSecondAction aa _ ha hrF.1)
  have hz : ∀ x ∉ tsupport F.val, PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F x = 0 := by
    intro x hx
    have hxA : x ∉ tsupport FA.val := fun h => hx (hsub h)
    have hzA := nativeZeroHalf_eq_zero_off g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q FA x hxA
    have hzF : ∀ y ∉ tsupport F.val, ZH hreg δ0 W g2 δr Ar p hδr hAr q F y = 0 :=
      fun y hy => nativeZeroHalf_eq_zero_off g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p hδr hAr q F y hy
    have hAz := coordinateSecondAction_eq_zero_off aa _ (tsupport F.val) (isClosed_tsupport F.val) hzF x hx
    dsimp only [FA] at hzA
    simp only [nativeZeroPhysicalCommutatorHalf,hzA,hAz,sub_self]
  have hSupp : Function.support (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    exact hx (hz x hx')
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩

/-- Full SphereL2 physical output with no angular output restriction. -/
def nativeZeroPhysicalCommutatorOut
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F x)
local notation "PO" => nativeZeroPhysicalCommutatorOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem nativeZeroPhysicalCommutatorOut_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F x)) =
      scalarZeroCoordinateCommutatorSum aa (fun y => CZc g2 δr Ar p q y) (UF F) x :=
  (sphereSobolevHalfToSphereL2L_negative_compatibility hO hD _).trans
    (congrFun (nativeZeroPhysicalCommutator_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq aa ha F hTF) x)

theorem nativeZeroPhysicalCommutatorOut_regular
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (aa : Fin 3 → Fin 3 → R3 → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (aa i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ∧
      tsupport (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ⊆ tsupport F.val ∧
      HasCompactSupport (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) := by
  have hr := nativeZeroPhysicalCommutator_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq aa ha F hTF
  have hs : ContDiff ℝ ∞ (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hr.1
  have hSupp : Function.support (PO hreg δ0 W g2 δr Ar p hδr hAr q aa ha F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    apply hx
    have hz : PC hreg δ0 W g2 δr Ar p hδr hAr q aa ha F x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx' (hr.2.1 ht))
    simp only [nativeZeroPhysicalCommutatorOut,hz,map_zero]
  exact ⟨hs,closure_minimal hSupp (isClosed_tsupport F.val),F.property.2.1.mono' hSupp⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroPhysicalCommutatorGraph
