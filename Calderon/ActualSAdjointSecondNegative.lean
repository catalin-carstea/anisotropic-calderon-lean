import Calderon.ActualReverseELowInputDerivative
import Calderon.ActualSAdjointAngularDoubleNegative

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondNegative
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualHigherSFormation
  ActualGeneratorEPairedGainedEndpoints ActualReverseEHigherLift
  ActualCommonFirstWordQuadraticAdjoint ActualHigherSSecondAdjoint ActualHigherSAdjointFormation
  ActualReverseELowInputDerivative ActualSAdjointAngularDoubleNegative
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  SphereHarmonic.DegreeGraphLifting ActualNormalizedSecondMetricDrift

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
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
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "Uin" => higherSInput hO hD
local notation "VR" => reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TS" F:max => tsupport (F : R3 → SphereL2)

/-- Exact density-multiplied negative Second field, retaining both degree corrections. -/
def secondAdjointDensityNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  let R := referenceRadius dr Ar p L
  let μ := referenceDensityFamily g L (q,x)
  let aij := secondCoefficient g g2 L q dr Ar p
  let fi := referenceRadiusHorizontalLogDerivative g L q R x
  let Γ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j
  let er := fun i : Fin 3 => eH i ((Tq dr Ar p q) x) (Uin F x)
  let D := fun i : Fin 3 => referenceHighWeightedHorizontalAction g L q R (Uin F) x i
  let BU := (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F x) : Half)
  let Wr := fun i j : Fin 3 =>
    (eL i ((Tq dr Ar p q) x) (IH (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) j))) +
      (fderiv ℝ (fun z => eL i ((Tq dr Ar p q) z)) x (referenceMetricGramFrame g L (q,x) j))
        (IH (Uin F x))) +
    referenceLowerHorizontalAngularL g L q x j (er i) +
    fi j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)
  let row1 : Fin 3 → Fin 3 → Neg := fun i j =>
    (-(μ*aij i j x)) • eL j ((Tq dr Ar p q) x) (D i) +
      (2*(μ*aij i j x*fi i)) • eL j ((Tq dr Ar p q) x) BU -
      densityDerivativeCoefficient g L q i (aij i j) x • eL j ((Tq dr Ar p q) x) (IH (Uin F x))
  let row2 : Fin 3 → Fin 3 → Neg := fun i j =>
    (-(μ*aij i j x)) • Wr i j +
      (2*(μ*aij i j x*fi j)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg) -
      densityDerivativeCoefficient g L q j (aij i j) x • JL (er i)
  (∑ i : Fin 3, ∑ j : Fin 3,
    (row1 i j+row2 i j+(μ*aij i j x*fi i) • JL (er j) -
      ∑ k : Fin 3, (μ*aij i j x*Γ i j k) • JL (er k))) +
    ∑ i : Fin 3, (μ*((R x)^2*normalizedSecondDriftFrameJoint g g2 L i (q,x))) • JL (er i)

local notation "SDN" => secondAdjointDensityNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The original density normalization of the complete negative Second field. -/
def secondAdjointNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  (referenceDensityFamily g L (q,x))⁻¹ • SDN g2 dr Ar p q F x

local notation "SN" => secondAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RD" => revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RS" => revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UD" => higherSReferenceInput hO hD g L hg
local notation "UB" => higherSDegreeInput hO hD

attribute [local irreducible] reverseEHigh reverseELow sphereSobolevInclusionL

/-- Exact full density Second graph on the original input support, with no graph premise. -/
theorem secondAdjointDensityNegative_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F) :
    JL (RD hreg δ0 W g2 dr Ar p hdr hAr q F x) = SDN g2 dr Ar p q F x := by
  have hE (j : Fin 3) (v : Hi) :
      JL (eH j ((Tq dr Ar p q) x) v) = eL j ((Tq dr Ar p q) x) (IH v) :=
    Cm.rev.compat j _ (hT x hx) v
  have hV (i : Fin 3) : IH (VR hreg δ0 W dr Ar p q F i x) =
      eH i ((Tq dr Ar p q) x) (Uin F x) :=
    reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm.rev dr Ar p q F hT i x
  have hUD (i : Fin 3) : IH (UD dr Ar p hdr hAr q F i x) =
      referenceHighWeightedHorizontalAction g L q (referenceRadius dr Ar p L) (Uin F) x i := by
    have hInc := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (coreReferenceInput hO hD g hg L q dr Ar p i hdr hAr F) x
    have hDict := referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q
      dr Ar p hdr hAr F x i
    exact hInc.trans hDict.symm
  have hUB : IH (UB F x) = (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F x) : Half) :=
    inclusion_finiteCoreSobolevLift_coreDegree hO hD F x
  have hB (i : Fin 3) :
      JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W dr Ar p q F i x) : Half) =
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (eH i ((Tq dr Ar p q) x) (Uin F x)) : Neg) := by
    have hc := congrArg (fun D : Hi →L[ℝ] Neg => D (VR hreg δ0 W dr Ar p q F i x))
      sphereSobolevShiftedDegree_high_half_compatibility
    have hc' : JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W dr Ar p q F i x) : Half) =
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (IH (VR hreg δ0 W dr Ar p q F i x)) : Neg) := by
      simpa only [ContinuousLinearMap.comp_apply] using hc
    exact hc'.trans (congrArg (sphereSobolevShiftedDegreeL (1/2 : ℝ)) (hV i))
  have hHoriz (i j : Fin 3) := reverseE_weighted_horizontal_negative
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm dr Ar p hdr hAr q F hT x hx j i
  dsimp only [revSecondDensityHalf,secondAdjointDensityNegative]
  simp only [map_add,map_sub,map_smul,map_sum,hE,hV,hUD,hUB,hB,hHoriz]

/-- Original normalized Second Half field has exactly the constructed negative image. -/
theorem secondAdjointNegative_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F) :
    JL (RS hreg δ0 W g2 dr Ar p hdr hAr q F x) = SN g2 dr Ar p q F x := by
  have hDen := secondAdjointDensityNegative_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 dr Ar p hdr hAr q F hT x hx
  exact (map_smul JL (referenceDensityFamily g L (q,x))⁻¹ _).trans
    (congrArg (fun v : Neg => (referenceDensityFamily g L (q,x))⁻¹ • v) hDen)

/-- Full original Second+Angular+Double S-adjoint negative field, on the same data and input. -/
def fullAdjointNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  SN g2 dr Ar p q F x +
    angularAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (Uin F x) +
    doubleAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (Uin F x)

/-- Full original S-adjoint source dictionary; all outputs and all ordered terms retained. -/
theorem fullAdjointNegative_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F) :
    JL (higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 dr Ar p hdr hAr q F x) =
        fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x := by
  have hs := secondAdjointNegative_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 dr Ar p hdr hAr q F hT x hx
  have ha := revAngularHalf_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 dr Ar p q F x (hT x hx)
  have hd := revDoubleHalf_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 dr Ar p q F x (hT x hx)
  simp only [higherSAdjointHalf,fullAdjointNegative,map_add,hs,ha,hd]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondNegative
