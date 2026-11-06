import Calderon.ActualHigherSSecondHalfPrincipal
import Calderon.ActualRaisingEHighGraph
/- Root; exact source expansion precedes this file in UPFRONT.md. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPrincipalPhysicalForms
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def gramHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramHighModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def gramLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gramHighNormed gramHighModule gramLowNormed gramLowModule

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RevRoom" => ActualReverseEHigherLift.ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BG" => (Sum.inr () : Generator)

local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "OH" => ActualConnectionGramCancellation.connectionHigh g L
local notation "OL" => ActualConnectionGramCancellation.connectionLow g L
local notation "COH" => ActualConnectionGramCancellation.connectionCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
local notation "BL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)

attribute [local irreducible] canonicalHigh reverseEHigh sphereSobolevInclusionL sphereSobolevDualPairing
  sphereSobolevHalfToSphereL2L ActualHigherSFormation.higherSInput
  ActualHigherSFormation.higherSReferenceInput ActualHigherSFormation.higherSRaisingInput
  referenceHighWeightedHorizontalAction raisingHigh sphereSobolevAngularCoordinateTransposeL

private lemma physical_add {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (K : V →L[ℝ] E) (u : E) (v w : V) :
    ⟪u,K (v+w)⟫_ℝ = ⟪u,K v⟫_ℝ+⟪u,K w⟫_ℝ := by
  rw [map_add,inner_add_right]

private lemma physical_weighted_rows {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (K : V →L[ℝ] E) (u : E) (r : ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → Fin 3 → V) (b : Fin 3 → Fin 3 → ℝ)
    (h : ∀ i j, ⟪u,K (v i j)⟫_ℝ = b i j) :
    ⟪u,K (r • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • v i j)⟫_ℝ =
      r * ∑ i : Fin 3, ∑ j : Fin 3, Q i j*b i j := by
  simp only [map_smul,map_sum,inner_smul_right,inner_sum,h]

/-- Exact one-pivot physical identity, with arbitrary genuine Hi input v. -/
theorem finite_physical_e_pivot (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (t : Tpar) (ht : t ∈ ParamRoom δ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (i : Fin 3) (v : Hi) :
    ⟪F.val x,KL (EH i t v)⟫_ℝ = ⟪KL (IH v),KL (eH i t (Uin F x))⟫_ℝ := by
  have hd : KL (IH (Uin F x)) = F.val x := by
    simpa only [ActualHigherSFormation.higherSInput] using
      ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F x
  have hp := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  calc
    ⟪F.val x,KL (EH i t v)⟫_ℝ = ⟪KL (IH (Uin F x)),KL (EH i t v)⟫_ℝ :=
      congrArg (fun z : SphereL2 => ⟪z,KL (EH i t v)⟫_ℝ) hd.symm
    _ = ⟪KL (EH i t v),KL (IH (Uin F x))⟫_ℝ := real_inner_comm _ _
    _ = PP (EH i t v) (JL (IH (Uin F x))) := (hp _ _).symm
    _ = PP (IH v) (JL (eH i t (Uin F x))) := Cm.pivot i t ht v (Uin F x)
    _ = ⟪KL (IH v),KL (eH i t (Uin F x))⟫_ℝ := hp _ _

/-- Ordered principal sum; an internal input graph, discharged by native finite inputs below. -/
theorem ordered_principal_physical_gram (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (t : Tpar) (ht : t ∈ ParamRoom δ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (V : Fin 3 → Hi) (D : Fin 3 → Half)
    (hVD : ∀ j, IH (V j) = D j) :
    ⟪F.val x,KL (r • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • (EH i t (V j)+EH j t (V i)))⟫_ℝ =
      r * ∑ i : Fin 3, ∑ j : Fin 3, Q i j *
        (⟪KL (D j),KL (eH i t (Uin F x))⟫_ℝ+⟪KL (D i),KL (eH j t (Uin F x))⟫_ℝ) := by
  apply physical_weighted_rows
  intro i j
  have hi := finite_physical_e_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm t ht F x i (V j)
  have hj := finite_physical_e_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm t ht F x j (V i)
  calc
    ⟪F.val x,KL (EH i t (V j)+EH j t (V i))⟫_ℝ =
        ⟪F.val x,KL (EH i t (V j))⟫_ℝ+⟪F.val x,KL (EH j t (V i))⟫_ℝ := physical_add KL _ _ _
    _ = ⟪KL (IH (V j)),KL (eH i t (Uin F x))⟫_ℝ+
        ⟪KL (IH (V i)),KL (eH j t (Uin F x))⟫_ℝ := congrArg₂ (fun a b : ℝ => a+b) hi hj
    _ = _ := congrArg₂ (fun a b : ℝ => a+b)
      (congrArg (fun z : Half => ⟪KL z,KL (eH i t (Uin F x))⟫_ℝ) (hVD j))
      (congrArg (fun z : Half => ⟪KL z,KL (eH j t (Uin F x))⟫_ℝ) (hVD i))

/-- Literal original second-S principal physical form, retaining the weighted D_j and both Q orders. -/
theorem second_principal_physical_gram (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (ht : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ⟪F.val x,KL (ActualHigherSSecondHalfPrincipal.secondHalfPrincipal
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W g2 δr Ar p hδr hAr q F x)⟫_ℝ =
      (referenceRadius δr Ar p L x)^2 * ∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
          (⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F) x j),
             KL (eH i ((Tq δr Ar p q) x) (Uin F x))⟫_ℝ+
           ⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F) x i),
             KL (eH j ((Tq δr Ar p q) x) (Uin F x))⟫_ℝ) := by
  have hVD (j : Fin 3) : IH (ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F j x) =
      referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F) x j := by
    simpa only [ActualHigherSFormation.higherSReferenceInput] using
      ActualHigherSSecondAdjoint.referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F j x
  exact ordered_principal_physical_gram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm ((Tq δr Ar p q) x) ht F x ((referenceRadius δr Ar p L x)^2)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun j => ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F j x)
    (fun j => referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F) x j) hVD

local notation "UA" => ActualHigherSFormation.higherSRaisingInput hF hO hD
local notation "AH" => raisingHigh hF hO hD

/-- Literal angular-S principal physical form, with native raising input and no lift norm. -/
theorem angular_principal_physical_gram (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (ht : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ⟪F.val x,KL (referenceRadius δr Ar p L x • ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        (EH i ((Tq δr Ar p q) x) (UA F j x)+EH j ((Tq δr Ar p q) x) (UA F i x)))⟫_ℝ =
      referenceRadius δr Ar p L x * ∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
          (⟪KL (AH j (Uin F x)),KL (eH i ((Tq δr Ar p q) x) (Uin F x))⟫_ℝ+
           ⟪KL (AH i (Uin F x)),KL (eH j ((Tq δr Ar p q) x) (Uin F x))⟫_ℝ) := by
  have hVA (j : Fin 3) : IH (UA F j x) = AH j (Uin F x) := by
    simpa only [ActualRaisingEHighGainedEndpoints.angularTranspose_threeHalf_eq_raisingHigh] using
      ActualHigherSAngularAdjoint.raisingInput_inclusion hF hO hD F j x
  exact ordered_principal_physical_gram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm ((Tq δr Ar p q) x) ht F x (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) (fun j => UA F j x)
    (fun j => AH j (Uin F x)) hVA

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPrincipalPhysicalForms
