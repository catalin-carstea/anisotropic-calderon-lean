import Calderon.ActualSobolevDegreeGraphLifting
import Calderon.ActualGeneratorEHighSmoothGerms
import Calderon.ActualGeneratorEHighGainedGraph
import Calderon.ActualFullECanonicalEndpoints
import Calderon.ActualAngularHighDraft
import Calderon.ActualAngularPiDraft
import Calderon.ActualPhysicalDensityErrorDecomposition
import Calderon.ActualNativeMovingLocalRemainderCompatibility
import Calderon.ActualNativeMovingAdjointMixedJNegativeInclusion
import Calderon.ActualFinitePhysicalModelErrorDictionary
import Calderon.ActualNativePhysicalModelInputDictionary
import Calderon.SphereSobolevHalfWeightedGraphLowering
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualFinitePhysicalWeakSquaredNorm
import Calderon.ActualLowerMovingBoundaryFamily
import Calderon.ActualWeightedHorizontalActions
import Calderon.ActualHorizontalGeometry
import Calderon.ReferenceRadiusScaling
import Calderon.ActualScalarPrincipalAdjoint

/-! Actual higher-S output formation: explicit degree-based Hi lift (Bessel lemmas),
global value identity by cases on support, smooth/support glue, literal Second/Angular/Double
Half fields, literal negative graph, actual SphereL2 output, support and weighted
integrability. Gamma smoothness comes from the joint connection API, the log-derivative uses
`hg`, and the final contract `higherSUniformFormationContract_proof` has room witnesses that
precede every profile parameter and whose only geometric premise on the input is
`T(x) ∈ ParamRoom δ` on the input support. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds SphereHarmonic.DegreeGraphLifting ConformalDepth ActualFiniteHarmonicModel
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1. Generic finite-lift and weighted-action facts -/
section Generic
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- A finite-core lift vanishing at one order vanishes at every order (same coordinates). -/
lemma finiteCoreSobolevLift_eq_zero_of_eq_zero (s t : ℝ)
    (G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (h : finiteCoreSobolevLift hO hD t G x = 0) :
    finiteCoreSobolevLift hO hD s G x = 0 := by
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,
    ← sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD t G x k, h, map_zero, map_zero]

/-- Pointwise zero input gives zero lift (by coefficients, without unfolding the lift). -/
lemma finiteCoreSobolevLift_eq_zero_of_eval (s : ℝ)
    (G : smoothCompactFiniteSphereCore hO hD) (x : R3) (h : G.val x = 0) :
    finiteCoreSobolevLift hO hD s G x = 0 := by
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift, h]
  simp

lemma eval_eq_zero_of_notMem_tsupport (G : smoothCompactFiniteSphereCore hO hD) (z : R3)
    (hz : z ∉ tsupport (G : R3 → SphereL2)) : G.val z = 0 :=
  image_eq_zero_of_notMem_tsupport hz

lemma notMem_tsupport_eventually (G : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ tsupport (G : R3 → SphereL2)) :
    ∀ᶠ z in 𝓝 x, z ∉ tsupport (G : R3 → SphereL2) :=
  (isClosed_tsupport _).isOpen_compl.mem_nhds hx
end Generic

private lemma maps_eq_of_input_zero (A B : Hi →L[ℝ] Neg) (v : Hi) (hv : v = 0) :
    A v = B v :=
  ((congrArg (fun b : Hi => A b) hv).trans A.map_zero).trans
    ((congrArg (fun b : Hi => B b) hv).trans B.map_zero).symm

private def higherSAlgebra {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (W D : Fin 3 → Fin 3 → E) (e : Fin 3 → E) (A EA EV : Fin 3 → Fin 3 → E) : E :=
  (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (W i j + D i j + f i • e j - ∑ k : Fin 3, Γ i j k • e k)) +
    r^2 • (∑ i : Fin 3, b i • e i)) +
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (A i j + EA i j)) +
    r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • EV i j)

private lemma map_higherSAlgebra (J : Half →L[ℝ] Neg)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (W D : Fin 3 → Fin 3 → Half) (e : Fin 3 → Half) (A EA EV : Fin 3 → Fin 3 → Half) :
    J (higherSAlgebra r Q b f Γ W D e A EA EV) =
      higherSAlgebra r Q b f Γ (fun i j => J (W i j)) (fun i j => J (D i j))
        (fun i => J (e i)) (fun i j => J (A i j)) (fun i j => J (EA i j))
        (fun i j => J (EV i j)) := by
  simp only [higherSAlgebra, map_add, map_sub, map_sum, map_smul]

/-- Weighted high/lower compatibility from the qualified unweighted action and the
degree high/half compatibility. The `f_i B` term (B = physical degree, k including 0) is kept. -/
lemma referenceWeightedHorizontalAction_inclusion (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (V : R3 → Hi) (y : R3) (i : Fin 3) (hV : DifferentiableAt ℝ V y) :
    JL (referenceHighWeightedHorizontalAction g L q R V y i) =
      referenceLowerWeightedHorizontalAction g L q R (fun x => IH (V x)) y i := by
  have h1 := referenceHorizontalAction_high_lower_compatibility g L q V y i hV
  have h2 : JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (V y) : Half) =
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) (IH (V y)) : Neg) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A (V y)) sphereSobolevShiftedDegree_high_half_compatibility
  show JL (referenceHighHorizontalAction g L q V y i +
      referenceRadiusHorizontalLogDerivative g L q R y i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (V y) : Half)) =
    referenceLowerHorizontalAction g L q (fun x => IH (V x)) y i +
      referenceRadiusHorizontalLogDerivative g L q R y i •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (IH (V y)) : Neg)
  calc
    JL (referenceHighHorizontalAction g L q V y i +
        referenceRadiusHorizontalLogDerivative g L q R y i •
          (sphereSobolevShiftedDegreeL (3/2 : ℝ) (V y) : Half)) =
        JL (referenceHighHorizontalAction g L q V y i) +
          referenceRadiusHorizontalLogDerivative g L q R y i •
            JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (V y)) := by
      exact (map_add JL _ _).trans
        (congrArg (fun z : Neg => JL (referenceHighHorizontalAction g L q V y i)+z)
          (map_smul JL _ _))
    _ = _ := congrArg₂ (fun x z : Neg => x + referenceRadiusHorizontalLogDerivative g L q R y i • z) h1 h2

/-- A field vanishing near `z` has zero weighted action at `z`. -/
lemma referenceHighWeightedHorizontalAction_eq_zero_of_eventually (g : MatrixField)
    (L q : ℝ) (R : R3 → ℝ) (V : R3 → Hi) (z : R3) (i : Fin 3)
    (hV : V =ᶠ[𝓝 z] fun _ => (0 : Hi)) :
    referenceHighWeightedHorizontalAction g L q R V z i = 0 := by
  have hz : V z = 0 := hV.self_of_nhds
  have hd : fderiv ℝ V z = 0 := hV.fderiv_eq.trans (fderiv_const_apply _)
  show IH (fderiv ℝ V z (referenceMetricGramFrame g L (q,z) i)) +
      referenceHighHorizontalAngularL g L q z i (V z) +
      referenceRadiusHorizontalLogDerivative g L q R z i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (V z) : Half) = 0
  simp only [hd, hz, ContinuousLinearMap.zero_apply, map_zero, smul_zero, add_zero]

/-- Gamma smoothness from the joint connection API. -/
lemma contDiff_referenceGramConnectionSlice (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i j k : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j) := by
  have hX := contDiff_referenceMetricGramFrame g hg L i
  have hJ := ActualHorizontalNormBridge.contDiff_referenceFrameConnectionJoint g hg L
    (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) hX k j
  have he : (fun y : R3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j) =
      (fun z : ℝ × R3 => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) z k j) ∘
        (fun y : R3 => ((q,y) : ℝ × R3)) := by
    funext y
    exact (ActualHorizontalNormBridge.referenceFrameConnectionJoint_eq g hg L
      (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) (q,y) k j).symm
  rw [he]
  exact hJ.comp (contDiff_const.prodMk contDiff_id)

/-! ## 2. Literal negative subsums (copied term by term from `referencePhysicalDensityError`) -/
section Literal
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "MQ" => referenceHighAdjointMovingDifferenceQuotient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LQ" => referenceLowerAdjointMovingDifferenceQuotient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Ahi" => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
local notation "Alo" => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)

/-- Literal `USecond` of `referencePhysicalDensityError`. -/
def nativeHigherSSecondNegative (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → Hi) (y : R3) : Neg :=
  let Iout := JL
  let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
  let Eh := fun (i : Fin 3) (x : R3) => MQ q R x i
  let El := fun i : Fin 3 => LQ q R y i
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let f := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q R y i
  let r := R y
  let UE := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (E j) y i+
    ME i (D j y)+f i • Iout (E j y)-(∑ k : Fin 3, Gamma i j k • Iout (E k y))
  r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j)+
    r^2 • (∑ i : Fin 3, b i • Iout (E i y))

/-- Literal `UAngular` of `referencePhysicalDensityError`. -/
def nativeHigherSAngularNegative (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → Hi) (y : R3) : Neg :=
  let angularHighMap := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let angularLowMap := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let Eh := fun (i : Fin 3) (x : R3) => MQ q R x i
  let El := fun i : Fin 3 => LQ q R y i
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let r := R y
  let UA := fun i j : Fin 3 => angularLowMap i (E j y)+ME i (angularHighMap j (u y))
  r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j)

/-- Literal `UDouble` of `referencePhysicalDensityError` (order `Elow_i (E_j)` kept). -/
def nativeHigherSDoubleNegative (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → Hi) (y : R3) : Neg :=
  let Eh := fun (i : Fin 3) (x : R3) => MQ q R x i
  let El := fun i : Fin 3 => LQ q R y i
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let r := R y
  let UEE := fun i j : Fin 3 => ME i (E j y)
  r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)

/-- The actual higher S negative: `USecond + UAngular + UDouble`, literal. -/
def nativeHigherSNegative (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → Hi) (y : R3) : Neg :=
  nativeHigherSSecondNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y +
  nativeHigherSAngularNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y +
  nativeHigherSDoubleNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y

/-! ## 3. Explicit degree-based Hi lift and Half fields, actual radius -/
section Formation
variable (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
include hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q

local notation "RR" => referenceRadius δr Ar p L

/-- Profile map `t(y) = ((q,(y,R y)), dR y)`. -/
def higherSParam (x : R3) : Tpar := ((q,(x,RR x)), fderiv ℝ RR x)
/-- Finite input `u = finiteLiftHi F0`. -/
def higherSInput (F0 : smoothCompactFiniteSphereCore hO hD) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
/-- `uB = finiteLiftHi (coreDegree F0)`, with `I uB = B_hi u`. -/
def higherSDegreeInput (F0 : smoothCompactFiniteSphereCore hO hD) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
/-- `uD_j = finiteLiftHi (coreReferenceInput_j F0)`, with `I uD_j = D_j u`. -/
def higherSReferenceInput (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreReferenceInput hO hD g hg L q δr Ar p j hδr hAr F0)
/-- `uA_j = finiteLiftHi (coreRaising_j F0)`, with `I uA_j = Ahi_j u`. -/
def higherSRaisingInput (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) : R3 → Hi :=
  finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRaising hO hD hF j F0)

local notation "T" => higherSParam L δr Ar p q
local notation "U" => higherSInput hO hD
local notation "UB" => higherSDegreeInput hO hD
local notation "UD" => higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q
local notation "UA" => higherSRaisingInput hF hO hD

/-- The explicit chosen Hi lift on ALL of R3 (no choice):
`V_j = BesselOrder Half Hi (C_B,j u + Ehi_j uB + Ehi_j u)`, `C_B,j = generatorEHigh (inr ())`. -/
def higherSLift (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) : Hi :=
  sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
    (CGE hreg δ0 W (Sum.inr ()) j (T x) (U F0 x) + EH j (T x) (UB F0 x) + EH j (T x) (U F0 x))

local notation "V" => higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q

/-- `SecondWordHalf_ij = Dhi_i V_j + Ehi_i uD_j + f_i e_j - Σ_k Γ_ijk e_k`, `e_j = I V_j`. -/
def higherSSecondWordHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (F0 : smoothCompactFiniteSphereCore hO hD) (i j : Fin 3) (y : R3) : Half :=
  referenceHighWeightedHorizontalAction g L q RR (V hreg δ0 W F0 j) y i +
    EH i (T y) (UD F0 j y) +
    referenceRadiusHorizontalLogDerivative g L q RR y i • IH (V hreg δ0 W F0 j y) -
    ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j • IH (V hreg δ0 W F0 k y)

def higherSSecondHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : Half :=
  (RR y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      higherSSecondWordHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
        hreg δ0 W F0 i j y) +
  (RR y)^2 • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • IH (V hreg δ0 W F0 i y))

def higherSAngularHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : Half :=
  RR y • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (Ahi i (V hreg δ0 W F0 j y) + EH i (T y) (UA F0 j y)))

def higherSDoubleHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : Half :=
  (RR y)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j • EH i (T y) (V hreg δ0 W F0 j y))

/-- The actual chosen higher-S Half field. -/
def nativeHigherSHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : Half :=
  higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
      hreg δ0 W g2 F0 y +
    higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q
      hreg δ0 W g2 F0 y +
    higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q
      hreg δ0 W g2 F0 y

/-- The actual SphereL2 output via the qualified Half→L2 map. -/
def nativeHigherSOut (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD
    (nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
      hreg δ0 W g2 F0 y)

local notation "SHalf" => nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
local notation "SOut" => nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
local notation "NEG" => nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Original geometric room data at one base point (q fixed, actual radius).
Intermediate glue only: the final contract derives the first three fields from the fourth. -/
def HigherSRoomAt (δ : ℝ) (x : R3) : Prop :=
  ‖x-y0‖ ≤ ρ ∧ (∀ θ ∈ Icc (0 : ℝ) 1, (q,(x,θ*RR x)) ∈ Ω) ∧
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((x,RR x),ξ.val))).IsInvertible) ∧
    T x ∈ ParamRoom δ

local notation "Room" => HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

lemma referenceRadius_ne_zero' (x : R3) : RR x ≠ 0 :=
  ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)

lemma contDiff_referenceRadius' : ContDiff ℝ ∞ RR :=
  ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr

lemma contDiff_higherSParam : ContDiff ℝ ∞ T := by
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  show ContDiff ℝ ∞ (fun x : R3 => (((q,(x,RR x)) : Pphys), fderiv ℝ RR x))
  exact (contDiff_const.prodMk (contDiff_id.prodMk hR)).prodMk
    (hR.fderiv_right (m := ∞) (by simp))

/-- The three geometric fields of `HigherSRoomAt` from parameter-room membership ALONE,
using the original segment lemma on `commonRoom δ0 ⊆ Ω` and the original guard's JacobiInv. -/
lemma higherSRoomAt_of_mem_paramRoom (δ0 δ dG : ℝ) (hδ0 : δ ≤ δ0) (hδG : δ ≤ dG)
    (hΩ0 : commonRoom y0 ρ δ0 ⊆ Ω)
    (hJac : ∀ z ∈ commonRoom y0 ρ dG, ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible)
    (x : R3) (hx : T x ∈ ParamRoom δ) : Room δ x := by
  have hc : ((q,(x,RR x)) : Pphys) ∈ commonRoom y0 ρ δ := hx.1
  have hb : x ∈ closedBall y0 ρ := hc.2.1
  have hc0 : ((q,(x,RR x)) : Pphys) ∈ commonRoom y0 ρ δ0 := commonRoom_mono y0 ρ hδ0 hc
  have hcG : ((q,(x,RR x)) : Pphys) ∈ commonRoom y0 ρ dG := commonRoom_mono y0 ρ hδG hc
  have hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(x,θ*RR x)) ∈ Ω :=
    segment_of_mem_commonRoom (hRoom := hΩ0) (p := ((q,(x,RR x)) : Pphys)) (hp := hc0)
  have hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((x,RR x),ξ.val))).IsInvertible :=
    hJac ((q,(x,RR x)) : Pphys) hcG
  have hn : ‖x-y0‖ ≤ ρ := by
    rw [mem_closedBall, dist_eq_norm] at hb
    exact hb
  exact ⟨hn, hSeg, hInv, hx⟩

/-! ### Off-support vanishing of all chosen inputs -/

lemma higherSInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3)
    (hz : z ∉ TS F0) : U F0 z = 0 :=
  finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F0 z
    (eval_eq_zero_of_notMem_tsupport hO hD F0 z hz)

lemma higherSInput_eventually_zero (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ TS F0) : U F0 =ᶠ[𝓝 x] fun _ => (0 : Hi) := by
  filter_upwards [notMem_tsupport_eventually hO hD F0 x hx] with z hz
  exact higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0 z hz

lemma higherSDegreeInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3)
    (hz : z ∉ TS F0) : UB F0 z = 0 := by
  have hU := higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0 z hz
  have h1 := inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 z
  have h2 := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreDegree hO hD F0) z
  have hB : (sphereSobolevShiftedDegreeL (3/2 : ℝ)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 z) : Half) = 0 := by
    have hU' : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 z = 0 := hU
    rw [hU', map_zero]
  exact finiteCoreSobolevLift_eq_zero_of_eq_zero hO hD (3/2 : ℝ) (1/2 : ℝ) _ z
    (h2.symm.trans (h1.trans hB))

lemma higherSRaisingInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3)
    (z : R3) (hz : z ∉ TS F0) : UA F0 j z = 0 := by
  have hU : finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 z = 0 :=
    higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hA := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F0 z j
  rw [hU, map_zero] at hA
  exact finiteCoreSobolevLift_eq_zero_of_eq_zero hO hD (3/2 : ℝ) (1/2 : ℝ) _ z hA.symm

lemma higherSReferenceInput_eq_zero (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3)
    (z : R3) (hz : z ∉ TS F0) : UD F0 j z = 0 := by
  have hW := referenceHighWeightedHorizontalAction_eq_zero_of_eventually g L q RR (U F0) z j
    (higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz)
  have hDict := referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q
    δr Ar p hδr hAr F0 z j
  exact finiteCoreSobolevLift_eq_zero_of_eq_zero hO hD (3/2 : ℝ) (1/2 : ℝ) _ z
    (hDict.symm.trans hW)

lemma higherSLift_eq_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (z : R3) (hz : z ∉ TS F0) :
    V hreg δ0 W F0 j z = 0 := by
  have hU := higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0 z hz
  have hB := higherSDegreeInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0 z hz
  simp only [higherSLift, hU, hB, map_zero, add_zero]

lemma higherSLift_eventually_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) (hx : x ∉ TS F0) :
    V hreg δ0 W F0 j =ᶠ[𝓝 x] fun _ => (0 : Hi) := by
  filter_upwards [notMem_tsupport_eventually hO hD F0 x hx] with z hz
  exact higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W F0 j z hz

/-! ### Pointwise room identities -/

attribute [local irreducible] canonicalHigh canonicalLow generatorEHigh sphereSobolevInclusionL

/-- Exact Bessel mechanism at one room point: `I V_j = Ehi_j u`. -/
lemma higherSLift_inclusion_of_graph (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3)
    (hGraph : ∀ v : Hi, JL (CGE hreg δ0 W (Sum.inr ()) j (T x) v) =
      generatorLow (Sum.inr ()) (EH j (T x) v) - EL j (T x) (generatorHigh (Sum.inr ()) v))
    (hCompat : ∀ v : Hi, JL (EH j (T x) v) = EL j (T x) (IH v)) :
    IH (V hreg δ0 W F0 j x) = EH j (T x) (U F0 x) := by
  have hG : JL (CGE hreg δ0 W (Sum.inr ()) j (T x) (U F0 x)) =
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) (EH j (T x) (U F0 x)) : Neg) -
        EL j (T x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 x) : Half) := hGraph (U F0 x)
  have hS := inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x
  have hB : EL j (T x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 x) : Half) =
      JL (EH j (T x) (UB F0 x)) :=
    (congrArg (EL j (T x)) hS.symm).trans (hCompat (UB F0 x)).symm
  have hDeg : (sphereSobolevShiftedDegreeL (1/2 : ℝ) (EH j (T x) (U F0 x)) : Neg) =
      JL (CGE hreg δ0 W (Sum.inr ()) j (T x) (U F0 x) + EH j (T x) (UB F0 x)) := by
    have hCombined := (map_add JL
      (CGE hreg δ0 W (Sum.inr ()) j (T x) (U F0 x))
      (EH j (T x) (UB F0 x))).trans
      (congrArg₂ (fun a b : Neg => a+b) hG hB.symm)
    exact (hCombined.trans (sub_add_cancel _ _)).symm
  exact inclusion_besselOrder_eq_of_half_degree_graph (EH j (T x) (U F0 x))
    (CGE hreg δ0 W (Sum.inr ()) j (T x) (U F0 x) + EH j (T x) (UB F0 x)) hDeg

lemma movingQuotient_eq_canonical_of_room (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ : ℝ) (x : R3) (hx : Room δ x) (i : Fin 3) :
    MQ q RR x i = EH i (T x) :=
  movingDifferenceQuotient_eq_canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg q hq RR (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr) x
    (by rw [mem_closedBall, dist_eq_norm]; exact hx.1)
    (ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)) hx.2.1 hx.2.2.1 i

/-- Original low quotient on included data, via the compatibility. -/
lemma lowerQuotient_inclusion_of_room (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ : ℝ) (x : R3) (hx : Room δ x) (i : Fin 3) (v : Hi) :
    LQ q RR x i (IH v) = JL (EH i (T x) v) := by
  have hp : (q,(x,RR x)) ∈ Ω := by
    simpa only [one_mul] using hx.2.1 1 ⟨zero_le_one, le_rfl⟩
  have hC := referenceAdjointMovingDifferenceQuotient_high_lower_compatibility
    (g := g) (L := L) (y0 := y0) (Φ := Φ) (B := B) (ε := ε) (C := C) (ρ := ρ) (H := H)
    (a := a) (w := w) (hData := hData) (hg := hg) (hcalc := hcalc) (hF := hF) (hO := hO)
    (hD := hD) (τ0 := τ0) hreg q hq RR x hx.1 i hx.2.2.1 hp
  have hQ := movingQuotient_eq_canonical_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
    τ0 δr Ar p hδr hAr q hreg hq δ x hx i
  exact (congrArg (fun A : Hi →L[ℝ] Neg => A v) hC).symm.trans
    (congrArg (fun A : Hi →L[ℝ] Half => JL (A v)) hQ)

/-! ### Room facts of the parents, collected at one δ (all discharged in §4) -/

/-- Exactly the parent outputs used: ordinary E ContDiffAt/compatibility, degree graph and
C_B ContDiffAt, all on the SAME parameter room. (Profile-independent content.) -/
def HigherSParentFacts (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) : Prop :=
  (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (EH i) t) ∧
  (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (EH i t u) = EL i t (IH u)) ∧
  (∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (CGE hreg δ0 W (Sum.inr ()) j t u) =
    generatorLow (Sum.inr ()) (EH j t u) - EL j t (generatorHigh (Sum.inr ()) u)) ∧
  (∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (CGE hreg δ0 W (Sum.inr ()) j) t)

local notation "Facts" => HigherSParentFacts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- GLOBAL value identity `I V_j = original E_j u`, by cases on support. -/
theorem higherSLift_inclusion_eq_movingQuotient (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hFacts : Facts hreg δ0 W δ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) (j : Fin 3) (x : R3) :
    IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x) := by
  by_cases hx : x ∈ TS F0
  · have hR := hRoom x hx
    rw [movingQuotient_eq_canonical_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
      τ0 δr Ar p hδr hAr q hreg hq δ x hR j]
    exact higherSLift_inclusion_of_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j x (hFacts.2.2.1 j (T x) hR.2.2.2)
      (hFacts.2.1 j (T x) hR.2.2.2)
  · simp only [higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j x hx,
      higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx, map_zero, map_zero]

/-- Family application glue: ContDiffAt at support points, locally zero off support. -/
lemma contDiff_family_apply (A : Tpar → Hi →L[ℝ] Half)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hA : ∀ x ∈ TS F0, ContDiffAt ℝ ∞ A (T x))
    (Wf : R3 → Hi) (hW : ContDiff ℝ ∞ Wf) (hW0 : ∀ z ∉ TS F0, Wf z = 0) :
    ContDiff ℝ ∞ (fun z => A (T z) (Wf z)) := by
  have hT := contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q
  refine contDiff_iff_contDiffAt.2 (fun x => ?_)
  by_cases hx : x ∈ TS F0
  · exact ((hA x hx).comp (f := T) x hT.contDiffAt).clm_apply hW.contDiffAt
  · have hzero : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : Half)) x := contDiffAt_const
    refine hzero.congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_eventually hO hD F0 x hx] with z hz
    rw [hW0 z hz, map_zero]

theorem contDiff_higherSLift (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (hFacts : Facts hreg δ0 W δ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) (j : Fin 3) :
    ContDiff ℝ ∞ (V hreg δ0 W F0 j) := by
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUB := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
  have hU0 := higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0
  have hUB0 := higherSDegreeInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0
  have h1 := contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q (CGE hreg δ0 W (Sum.inr ()) j) F0
    (fun x hx => hFacts.2.2.2 j (T x) (hRoom x hx).2.2.2) (U F0) hU hU0
  have h2 := contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q (EH j) F0
    (fun x hx => hFacts.1 j (T x) (hRoom x hx).2.2.2) (UB F0) hUB hUB0
  have h3 := contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q (EH j) F0
    (fun x hx => hFacts.1 j (T x) (hRoom x hx).2.2.2) (U F0) hU hU0
  exact (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)).contDiff.comp ((h1.add h2).add h3)

/-! ### Half-field smoothness and support -/

theorem contDiff_nativeHigherSHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) :
    ContDiff ℝ ∞ (SHalf hreg δ0 W g2 F0) := by
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hV := contDiff_higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts F0 hRoom
  have hV0 := higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W F0
  have hEAt (i : Fin 3) : ∀ x ∈ TS F0, ContDiffAt ℝ ∞ (EH i) (T x) :=
    fun x hx => hFacts.1 i (T x) (hRoom x hx).2.2.2
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) :=
    contDiff_const.prodMk contDiff_id
  have hQ (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (f := fun y : R3 => (q,y)) hqy
  have hb (i : Fin 3) : ContDiff ℝ ∞ (fun y => normalizedSecondDriftFrameJoint g g2 L i (q,y)) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (f := fun y : R3 => (q,y)) hqy
  have hΓ (i j k : Fin 3) : ContDiff ℝ ∞ (fun y => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j) :=
    contDiff_referenceGramConnectionSlice g hg L q i j k
  have hf (i : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceRadiusHorizontalLogDerivative g L q RR y i) :=
    contDiff_iff_contDiffAt.2 (fun y =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg RR (q,y) i
        hRR.contDiffAt (ne_of_gt (referenceRadius_pos δr Ar p L y hδr hAr))).comp y
          (contDiffAt_const.prodMk contDiffAt_id))
  have hIV (j : Fin 3) : ContDiff ℝ ∞ (fun y => IH (V hreg δ0 W F0 j y)) :=
    (IH).contDiff.comp (hV j)
  have hAV (i j : Fin 3) : ContDiff ℝ ∞ (fun y => Ahi i (V hreg δ0 W F0 j y)) :=
    (Ahi i).contDiff.comp (hV j)
  have hWV (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceHighWeightedHorizontalAction g L q RR (V hreg δ0 W F0 j) y i) :=
    contDiff_iff_contDiffAt.2 (fun y =>
      contDiffAt_referenceHighWeightedHorizontalAction g hg L q RR (V hreg δ0 W F0 j) y i
        hRR.contDiffAt (ne_of_gt (referenceRadius_pos δr Ar p L y hδr hAr)) (hV j).contDiffAt)
  have hED (i j : Fin 3) : ContDiff ℝ ∞ (fun y => EH i (T y) (UD F0 j y)) :=
    contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q (EH i) F0 (hEAt i) (UD F0 j)
      (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) _)
      (higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 j)
  have hEA (i j : Fin 3) : ContDiff ℝ ∞ (fun y => EH i (T y) (UA F0 j y)) :=
    contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q (EH i) F0 (hEAt i) (UA F0 j)
      (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) _)
      (higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 j)
  have hEV (i j : Fin 3) : ContDiff ℝ ∞ (fun y => EH i (T y) (V hreg δ0 W F0 j y)) :=
    contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q (EH i) F0 (hEAt i) (V hreg δ0 W F0 j) (hV j) (hV0 j)
  have hSW (i j : Fin 3) : ContDiff ℝ ∞ (higherSSecondWordHalf hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 i j) :=
    (((hWV i j).add (hED i j)).add ((hf i).smul (hIV j))).sub
      (ContDiff.sum (fun k _ => (hΓ i j k).smul (hIV k)))
  have hSecond : ContDiff ℝ ∞ (higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 F0) :=
    ((hRR.pow 2).smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (hQ i j).smul (hSW i j))))).add
    ((hRR.pow 2).smul (ContDiff.sum (fun i _ => (hb i).smul (hIV i))))
  have hAngular : ContDiff ℝ ∞ (higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q hreg δ0 W g2 F0) :=
    hRR.smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (hQ i j).smul ((hAV i j).add (hEA i j)))))
  have hDouble : ContDiff ℝ ∞ (higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q hreg δ0 W g2 F0) :=
    (hRR.pow 3).smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (hQ i j).smul (hEV i j))))
  exact (hSecond.add hAngular).add hDouble

theorem nativeHigherSHalf_eq_zero (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD)
    (z : R3) (hz : z ∉ TS F0) : SHalf hreg δ0 W g2 F0 z = 0 := by
  have hV0 (j : Fin 3) := higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W F0 j z hz
  have hD0 (j : Fin 3) := higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q F0 j z hz
  have hA0 (j : Fin 3) := higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q F0 j z hz
  have hW0 (i j : Fin 3) : referenceHighWeightedHorizontalAction g L q RR
      (V hreg δ0 W F0 j) z i = 0 :=
    referenceHighWeightedHorizontalAction_eq_zero_of_eventually g L q RR _ z i
      (higherSLift_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q hreg δ0 W F0 j z hz)
  simp only [nativeHigherSHalf, higherSSecondHalf, higherSAngularHalf, higherSDoubleHalf,
    higherSSecondWordHalf, hV0, hD0, hA0, hW0, map_zero, smul_zero, add_zero, sub_zero,
    Finset.sum_const_zero]

private lemma endpoint_compatibility_at_support (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (y : R3) (v : Hi) (hyRoom : y ∈ TS F0 → Room δ y)
    (hvzero : y ∉ TS F0 → v = 0) (i : Fin 3) :
    LQ q RR y i (IH v) = JL (EH i (T y) v) ∧
      JL (Ahi i v) = Alo i (IH v) := by
  by_cases hy : y ∈ TS F0
  · exact ⟨lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
        τ0 δr Ar p hδr hAr q hreg hq δ y (hyRoom hy) i v,
      referenceAngularCoordinateTranspose_high_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y (hyRoom hy).1 i v⟩
  · have hZ := hvzero hy
    have h1 := maps_eq_of_input_zero ((LQ q RR y i).comp (IH))
      ((JL).comp (EH i (T y))) v hZ
    have h2 := maps_eq_of_input_zero ((JL).comp (Ahi i))
      ((Alo i).comp (IH)) v hZ
    exact ⟨h1, h2⟩

/-! ### Literal negative graph -/

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceLowerAdjointMovingDifferenceQuotient sphereSobolevAngularCoordinateTransposeL
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceFrameConnectionCoefficient referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
  referenceRadiusHorizontalLogDerivative normalizedSecondDriftFrameJoint higherSLift higherSInput
  higherSReferenceInput higherSRaisingInput higherSParam

private def HigherSGraphFields (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : Prop :=
  (∀ i j : Fin 3, JL (referenceHighWeightedHorizontalAction g L q RR (V hreg δ0 W F0 j) y i) =
    referenceLowerWeightedHorizontalAction g L q RR (fun x => MQ q RR x j (U F0 x)) y i) ∧
  (∀ i j : Fin 3, JL (EH i (T y) (UD F0 j y)) =
    LQ q RR y i (referenceHighWeightedHorizontalAction g L q RR (U F0) y j)) ∧
  (∀ i j : Fin 3, JL (EH i (T y) (UA F0 j y)) = LQ q RR y i (Ahi j (U F0 y))) ∧
  (∀ i j : Fin 3, JL (EH i (T y) (V hreg δ0 W F0 j y)) = LQ q RR y i (MQ q RR y j (U F0 y))) ∧
  (∀ i j : Fin 3, JL (Ahi i (V hreg δ0 W F0 j y)) = Alo i (MQ q RR y j (U F0 y)))

local notation "GraphFields" => HigherSGraphFields hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q

private lemma higherS_graph_fields (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hFacts : Facts hreg δ0 W δ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) (y : R3) : GraphFields hreg δ0 W F0 y := by
  have hV := contDiff_higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts F0 hRoom
  have hE (j : Fin 3) (x : R3) : IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x) :=
    higherSLift_inclusion_eq_movingQuotient hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts F0 hRoom j x
  have hEfun (j : Fin 3) : (fun x => IH (V hreg δ0 W F0 j x)) =
      (fun x => MQ q RR x j (U F0 x)) := funext (hE j)
  -- weighted Second: global function identity, differentiated legitimately
  have hW (i j : Fin 3) : JL (referenceHighWeightedHorizontalAction g L q RR
      (V hreg δ0 W F0 j) y i) = referenceLowerWeightedHorizontalAction g L q RR
        (fun x => MQ q RR x j (U F0 x)) y i := by
    rw [referenceWeightedHorizontalAction_inclusion g L q RR _ y i
      ((hV j).differentiable (by simp) y), hEfun j]
  -- the three Elow-terms and the angular term, by cases on support
  have hDt (i j : Fin 3) : JL (EH i (T y) (UD F0 j y)) =
      LQ q RR y i (referenceHighWeightedHorizontalAction g L q RR (U F0) y j) := by
    by_cases hy : y ∈ TS F0
    · have hDict := referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q
        δr Ar p hδr hAr F0 y j
      have hInc := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
        (by norm_num) (coreReferenceInput hO hD g hg L q δr Ar p j hδr hAr F0) y
      have hIn : referenceHighWeightedHorizontalAction g L q RR (U F0) y j = IH (UD F0 j y) := by
        simpa only [referenceHighWeightedHorizontalAction, higherSInput, higherSReferenceInput] using
          hDict.trans hInc.symm
      have hLow := lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
        τ0 δr Ar p hδr hAr q hreg hq δ y (hRoom y hy) i (UD F0 j y)
      exact hLow.symm.trans (congrArg (fun b : Half => LQ q RR y i b) hIn.symm)
    · simp only [higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 j y hy,
        referenceHighWeightedHorizontalAction_eq_zero_of_eventually g L q RR _ y j
          (higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
            δr Ar p hδr hAr q F0 y hy), map_zero, map_zero, map_zero]
  have hAt (i j : Fin 3) : JL (EH i (T y) (UA F0 j y)) = LQ q RR y i (Ahi j (U F0 y)) := by
    by_cases hy : y ∈ TS F0
    · have hRaise := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F0 y j
      have hInc := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
        (by norm_num) (coreRaising hO hD hF j F0) y
      have hIn : Ahi j (U F0 y) = IH (UA F0 j y) := by
        simpa only [higherSInput, higherSRaisingInput] using hRaise.trans hInc.symm
      have hLow := lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
        τ0 δr Ar p hδr hAr q hreg hq δ y (hRoom y hy) i (UA F0 j y)
      exact hLow.symm.trans (congrArg (fun b : Half => LQ q RR y i b) hIn.symm)
    · simp only [higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 j y hy,
        higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 y hy, map_zero, map_zero, map_zero, map_zero]
  have hEndpoints (i j : Fin 3) := endpoint_compatibility_at_support hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg hq δ F0 y (V hreg δ0 W F0 j y)
    (fun hy => hRoom y hy)
    (fun hy => higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j y hy) i
  have hVt (i j : Fin 3) : JL (EH i (T y) (V hreg δ0 W F0 j y)) =
      LQ q RR y i (MQ q RR y j (U F0 y)) :=
    (hEndpoints i j).1.symm.trans (congrArg (fun b : Half => LQ q RR y i b) (hE j y))
  have hAng (i j : Fin 3) : JL (Ahi i (V hreg δ0 W F0 j y)) =
      Alo i (MQ q RR y j (U F0 y)) :=
    (hEndpoints i j).2.trans (congrArg (fun b : Half => Alo i b) (hE j y))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hW i j
  · intro i j
    exact hDt i j
  · intro i j
    exact hAt i j
  · intro i j
    exact hVt i j
  · intro i j
    exact hAng i j

/-- `J (nativeHigherSHalf y) = nativeHigherSNegative y` for the literal input `u = finiteLiftHi F0`,
at EVERY y: room compatibilities on support, local vanishing off support. -/
theorem nativeHigherSHalf_negative_graph (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hRoom : ∀ x ∈ TS F0, Room δ x) (y : R3) :
    JL (SHalf hreg δ0 W g2 F0 y) = NEG g2 q RR (U F0) y := by
  have hE (j : Fin 3) (x : R3) : IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x) :=
    higherSLift_inclusion_eq_movingQuotient hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts F0 hRoom j x
  have hFields := higherS_graph_fields hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ hFacts F0 hRoom y
  have hW := hFields.1
  have hDt := hFields.2.1
  have hAt := hFields.2.2.1
  have hVt := hFields.2.2.2.1
  have hAng := hFields.2.2.2.2
  let r : ℝ := RR y
  let Q : Fin 3 → Fin 3 → ℝ := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let b : Fin 3 → ℝ := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let f : Fin 3 → ℝ := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q RR y i
  let Γ : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let WH : Fin 3 → Fin 3 → Half := fun i j : Fin 3 => referenceHighWeightedHorizontalAction g L q RR (V hreg δ0 W F0 j) y i
  let DH : Fin 3 → Fin 3 → Half := fun i j : Fin 3 => EH i (T y) (UD F0 j y)
  let eH : Fin 3 → Half := fun j : Fin 3 => IH (V hreg δ0 W F0 j y)
  let AH : Fin 3 → Fin 3 → Half := fun i j : Fin 3 => Ahi i (V hreg δ0 W F0 j y)
  let EAH : Fin 3 → Fin 3 → Half := fun i j : Fin 3 => EH i (T y) (UA F0 j y)
  let EVH : Fin 3 → Fin 3 → Half := fun i j : Fin 3 => EH i (T y) (V hreg δ0 W F0 j y)
  let WN : Fin 3 → Fin 3 → Neg := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q RR
    (fun x => MQ q RR x j (U F0 x)) y i
  let DN : Fin 3 → Fin 3 → Neg := fun i j : Fin 3 => LQ q RR y i
    (referenceHighWeightedHorizontalAction g L q RR (U F0) y j)
  let eN : Fin 3 → Neg := fun j : Fin 3 => JL (MQ q RR y j (U F0 y))
  let AN : Fin 3 → Fin 3 → Neg := fun i j : Fin 3 => Alo i (MQ q RR y j (U F0 y))
  let EAN : Fin 3 → Fin 3 → Neg := fun i j : Fin 3 => LQ q RR y i (Ahi j (U F0 y))
  let EVN : Fin 3 → Fin 3 → Neg := fun i j : Fin 3 => LQ q RR y i (MQ q RR y j (U F0 y))
  have hSource : SHalf hreg δ0 W g2 F0 y = higherSAlgebra r Q b f Γ WH DH eH AH EAH EVH := rfl
  have hTarget : NEG g2 q RR (U F0) y = higherSAlgebra r Q b f Γ WN DN eN AN EAN EVN := rfl
  have ht := map_higherSAlgebra (JL) r Q b f Γ WH DH eH AH EAH EVH
  have hw : (fun i j => JL (WH i j)) = WN := funext (fun i => funext (fun j => hW i j))
  have hd : (fun i j => JL (DH i j)) = DN := funext (fun i => funext (fun j => hDt i j))
  have he : (fun i => JL (eH i)) = eN :=
    funext (fun i => congrArg (fun z : Half => JL z) (hE i y))
  have ha : (fun i j => JL (AH i j)) = AN := funext (fun i => funext (fun j => hAng i j))
  have hea : (fun i j => JL (EAH i j)) = EAN := funext (fun i => funext (fun j => hAt i j))
  have hev : (fun i j => JL (EVH i j)) = EVN := funext (fun i => funext (fun j => hVt i j))
  have hwd := congrArg₂ (fun (v d : Fin 3 → Fin 3 → Neg) =>
    higherSAlgebra r Q b f Γ v d (fun i => JL (eH i))
      (fun i j => JL (AH i j)) (fun i j => JL (EAH i j)) (fun i j => JL (EVH i j))) hw hd
  have hea2 := congrArg₂ (fun (e : Fin 3 → Neg) (a : Fin 3 → Fin 3 → Neg) =>
    higherSAlgebra r Q b f Γ WN DN e a (fun i j => JL (EAH i j))
      (fun i j => JL (EVH i j))) he ha
  have hev2 := congrArg₂ (fun (ea ev : Fin 3 → Fin 3 → Neg) =>
    higherSAlgebra r Q b f Γ WN DN eN AN ea ev) hea hev
  exact (congrArg (fun z : Half => JL z) hSource).trans
    (ht.trans (hwd.trans (hea2.trans (hev2.trans hTarget.symm))))

/-! ### Actual SphereL2 output -/

theorem nativeHigherSOut_negative_graph (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hRoom : ∀ x ∈ TS F0, Room δ x) (y : R3) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (SOut hreg δ0 W g2 F0 y)) = NEG g2 q RR (U F0) y :=
  (sphereSobolevHalfToSphereL2L_negative_compatibility hO hD _).trans
    (nativeHigherSHalf_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom y)

theorem nativeHigherSOut_regular (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) :
    ContDiff ℝ ∞ (SOut hreg δ0 W g2 F0) ∧
      tsupport (SOut hreg δ0 W g2 F0) ⊆ TS F0 ∧ HasCompactSupport (SOut hreg δ0 W g2 F0) := by
  have hS := contDiff_nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom
  have hSupp : Function.support (SOut hreg δ0 W g2 F0) ⊆ TS F0 := by
    intro z hz
    by_contra hz'
    apply hz
    show sphereSobolevHalfToSphereL2L hO hD (SHalf hreg δ0 W g2 F0 z) = 0
    rw [nativeHigherSHalf_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0 z hz', map_zero]
  -- `smoothCompactFiniteSphereCore` stores ContDiff, compact support, finite blocks
  have hF0 : HasCompactSupport (F0 : R3 → SphereL2) := F0.property.2.1
  exact ⟨(sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hS,
    closure_minimal hSupp (isClosed_tsupport _), hF0.mono' hSupp⟩

/-- Weighted integrability for any continuous weight. -/
theorem integrable_weighted_nativeHigherSOut (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) (mu : R3 → ℝ) (hmu : Continuous mu) :
    Integrable (fun y => mu y * ‖SOut hreg δ0 W g2 F0 y‖^2) (volume : Measure R3) := by
  have h := nativeHigherSOut_regular hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom
  exact integrable_weighted_norm_sq_of_continuous_compact mu hmu _ h.1.continuous h.2.2

/-- In particular with the actual density `rho = referenceDensityFamily (g,L,(q,y))`. -/
theorem integrable_density_nativeHigherSOut (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hRoom : ∀ x ∈ TS F0, Room δ x) :
    Integrable (fun y => referenceDensityFamily g L (q,y) * ‖SOut hreg δ0 W g2 F0 y‖^2)
      (volume : Measure R3) :=
  integrable_weighted_nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom _
    ((contDiff_referenceDensityFamily g hg L).continuous.comp
      (continuous_const.prodMk continuous_id))

/-! ### Bundled per-profile output conclusions -/

/-- Every actual output claim for one profile and one finite input (no finiteness of output,
no cut, no callback): Hi identity/CDF/support, Half CDF, Half and SphereL2 negative graphs,
SphereL2 CDF/tsupport/compact support, weighted and actual-density integrability. -/
def HigherSOutputConclusions (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (∀ j : Fin 3, ∀ x : R3, IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x)) ∧
  (∀ j : Fin 3, ContDiff ℝ ∞ (V hreg δ0 W F0 j) ∧ ∀ z ∉ TS F0, V hreg δ0 W F0 j z = 0) ∧
  ContDiff ℝ ∞ (SHalf hreg δ0 W g2 F0) ∧
  (∀ y : R3, JL (SHalf hreg δ0 W g2 F0 y) = NEG g2 q RR (U F0) y) ∧
  (∀ y : R3, sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
    (sphereSobolevZeroEquiv hO hD (SOut hreg δ0 W g2 F0 y)) = NEG g2 q RR (U F0) y) ∧
  (ContDiff ℝ ∞ (SOut hreg δ0 W g2 F0) ∧
    tsupport (SOut hreg δ0 W g2 F0) ⊆ TS F0 ∧ HasCompactSupport (SOut hreg δ0 W g2 F0)) ∧
  (∀ mu : R3 → ℝ, Continuous mu →
    Integrable (fun y => mu y * ‖SOut hreg δ0 W g2 F0 y‖^2) (volume : Measure R3)) ∧
  Integrable (fun y => referenceDensityFamily g L (q,y) * ‖SOut hreg δ0 W g2 F0 y‖^2)
    (volume : Measure R3)

theorem higherSOutputConclusions_of_facts (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hFacts : Facts hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hRoom : ∀ x ∈ TS F0, Room δ x) :
    HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  unfold HigherSOutputConclusions
  exact ⟨higherSLift_inclusion_eq_movingQuotient hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
      τ0 δr Ar p hδr hAr q hreg hq δ0 W δ hFacts F0 hRoom,
    fun j => ⟨contDiff_higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts F0 hRoom j,
      higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j⟩,
    contDiff_nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom,
    nativeHigherSHalf_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom,
    nativeHigherSOut_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom,
    nativeHigherSOut_regular hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom,
    integrable_weighted_nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom,
    integrable_density_nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom⟩

/-! ## 4. Discharging the parent facts on ONE common room (profile-dependent form) -/

/-- Folded contract. It is profile-dependent: δr Ar p q are section variables.
The stronger uniform, membership-only contract is `HigherSUniformFormationContract` below. -/
def HigherSFormationContract (hreg : FixedDirichletRegularity) (hq : q ∈ Icc (0 : ℝ) 1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    commonRoom y0 ρ δ ⊆ Ω ∧
    ∀ F0 : smoothCompactFiniteSphereCore hO hD, (∀ x ∈ TS F0, Room δ x) →
      (∀ j : Fin 3, ∀ x : R3, IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x)) ∧
      (∀ j : Fin 3, ContDiff ℝ ∞ (V hreg δ0 W F0 j) ∧ ∀ z ∉ TS F0, V hreg δ0 W F0 j z = 0) ∧
      (∀ y : R3, JL (SHalf hreg δ0 W g2 F0 y) = NEG g2 q RR (U F0) y) ∧
      (∀ y : R3, sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (SOut hreg δ0 W g2 F0 y)) = NEG g2 q RR (U F0) y) ∧
      (ContDiff ℝ ∞ (SOut hreg δ0 W g2 F0) ∧
        tsupport (SOut hreg δ0 W g2 F0) ⊆ TS F0 ∧ HasCompactSupport (SOut hreg δ0 W g2 F0)) ∧
      (∀ mu : R3 → ℝ, Continuous mu →
        Integrable (fun y => mu y * ‖SOut hreg δ0 W g2 F0 y‖^2) (volume : Measure R3)) ∧
      Integrable (fun y => referenceDensityFamily g L (q,y) * ‖SOut hreg δ0 W g2 F0 y‖^2)
        (volume : Measure R3)

theorem higherSFormationContract_proof (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (hq : q ∈ Icc (0 : ℝ) 1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    HigherSFormationContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq g2 hg2 := by
  let hEP := exists_commonRoom_actual_fullE_ordinary_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let δ0 := Classical.choose hEP
  have hE0 := Classical.choose_spec hEP
  have hδ0 : 0 < δ0 := hE0.1
  have hδ0ρ : δ0 ≤ ρ := hE0.2.1
  have hΩ0 : commonRoom y0 ρ δ0 ⊆ Ω := hE0.2.2.1
  let W := Classical.choose hE0.2.2.2
  have hW := Classical.choose_spec hE0.2.2.2
  let hGP := exists_commonRoom_actual_generator_E_high_graphs hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  let δ1 := Classical.choose hGP
  have hG1 := Classical.choose_spec hGP
  let hCP := exists_commonRoom_actual_generator_E_high_contDiffAt hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg δ0 hδ0 W
  let δ2 := Classical.choose hCP
  have hC2 := Classical.choose_spec hCP
  let δ := min δ1 δ2
  have hδ : 0 < δ := lt_min hG1.1 hC2.1
  have hδ1 : δ ≤ δ1 := min_le_left _ _
  have hδ2 : δ ≤ δ2 := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := hδ1.trans hG1.2.1
  have hSub0 := commonRoom_mono y0 ρ hδδ0
  have hSub1 := commonRoom_mono y0 ρ hδ1
  have hSub2 := commonRoom_mono y0 ρ hδ2
  have hFacts : Facts hreg δ0 W δ :=
    ⟨fun i t ht => (hW.1 i t ⟨hSub0 ht.1, ht.2⟩).1,
     fun i t ht u => (hW.2.1 i t ⟨hSub0 ht.1, ht.2⟩ u).1,
     fun j t ht u => hG1.2.2.2 (Sum.inr ()) j t ⟨hSub1 ht.1, ht.2⟩ u,
     fun j t ht => hC2.2.2.2 (Sum.inr ()) j t ⟨hSub2 ht.1, ht.2⟩⟩
  unfold HigherSFormationContract
  refine ⟨δ0, hδ0, W, δ, hδ, hδδ0, hδδ0.trans hδ0ρ, hSub0.trans hΩ0, ?_⟩
  intro F0 hRoom
  have hReg := nativeHigherSOut_regular hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom
  exact ⟨higherSLift_inclusion_eq_movingQuotient hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
      τ0 δr Ar p hδr hAr q hreg hq δ0 W δ hFacts F0 hRoom,
    fun j => ⟨contDiff_higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts F0 hRoom j,
      higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j⟩,
    nativeHigherSHalf_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom,
    nativeHigherSOut_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom,
    hReg,
    integrable_weighted_nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom,
    integrable_density_nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W δ hFacts g2 hg2 F0 hRoom⟩

end Formation

/-! ## 5. Uniform room before profile, membership-only input premise -/

/-- Room witnesses `δ0, W, δ` are chosen from the original geometry ONLY; then for EVERY
radius profile `(δr,Ar,p)`, every `q ∈ [0,1]` and every finite input `F0` whose profile map
lands in `ParamRoom δ` on `tsupport F0`, all actual output conclusions hold. -/
def HigherSUniformFormationContract (hreg : FixedDirichletRegularity) (g2 : MatrixField) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    commonRoom y0 ρ δ ⊆ Ω ∧
    ∀ (δr Ar : ℝ) (hδr : 0 < δr) (hAr : 0 < Ar) (p : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD,
        (∀ x ∈ tsupport (F0 : R3 → SphereL2),
          higherSParam L δr Ar p q x ∈
            ParamRoom δ) →
        HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
          δr Ar p hδr hAr q hreg δ0 W g2 F0

theorem higherSUniformFormationContract_proof (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    HigherSUniformFormationContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg g2 := by
  -- original full-E ordinary endpoints: δ0, segment room, W
  let hEP := exists_commonRoom_actual_fullE_ordinary_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let δ0 := Classical.choose hEP
  have hE0 := Classical.choose_spec hEP
  have hδ0 : 0 < δ0 := hE0.1
  have hδ0ρ : δ0 ≤ ρ := hE0.2.1
  have hΩ0 : commonRoom y0 ρ δ0 ⊆ Ω := hE0.2.2.1
  let W := Classical.choose hE0.2.2.2
  have hW := Classical.choose_spec hE0.2.2.2
  -- generator graph δ1 and generator smoothness δ2 for the SAME W
  let hGP := exists_commonRoom_actual_generator_E_high_graphs hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg hKernel δ0 hδ0 W
  let δ1 := Classical.choose hGP
  have hG1 := Classical.choose_spec hGP
  let hCP := exists_commonRoom_actual_generator_E_high_contDiffAt hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg δ0 hδ0 W
  let δ2 := Classical.choose hCP
  have hC2 := Classical.choose_spec hCP
  -- original finite room guard dG: JacobiInv on commonRoom dG
  let hRG := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let lam := Classical.choose hRG
  have hRG1 := Classical.choose_spec hRG
  let Lam := Classical.choose hRG1
  have hRG2 := Classical.choose_spec hRG1
  let dG := Classical.choose hRG2
  have hFin := Classical.choose_spec hRG2
  have hdG : 0 < dG := hFin.2.1
  have hJac : ∀ z ∈ commonRoom y0 ρ dG, ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible :=
    fun z hz => (hFin.2.2.2 z hz).2.2.2.2
  -- ONE shrunk room, before any profile or input
  let δ := min δ1 (min δ2 dG)
  have hδ : 0 < δ := lt_min hG1.1 (lt_min hC2.1 hdG)
  have hδ1 : δ ≤ δ1 := min_le_left _ _
  have hδ2 : δ ≤ δ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδG : δ ≤ dG := (min_le_right _ _).trans (min_le_right _ _)
  have hδδ0 : δ ≤ δ0 := hδ1.trans hG1.2.1
  have hSub0 := commonRoom_mono y0 ρ hδδ0
  have hSub1 := commonRoom_mono y0 ρ hδ1
  have hSub2 := commonRoom_mono y0 ρ hδ2
  unfold HigherSUniformFormationContract
  refine ⟨δ0, hδ0, W, δ, hδ, hδδ0, hδδ0.trans hδ0ρ, hSub0.trans hΩ0, ?_⟩
  intro δr Ar hδr hAr p q hq F0 hMem
  -- the parent facts do not depend on the profile: same proof for every (δr,Ar,p,q)
  have hFacts : HigherSParentFacts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W δ :=
    ⟨fun i t ht => (hW.1 i t ⟨hSub0 ht.1, ht.2⟩).1,
     fun i t ht u => (hW.2.1 i t ⟨hSub0 ht.1, ht.2⟩ u).1,
     fun j t ht u => hG1.2.2.2 (Sum.inr ()) j t ⟨hSub1 ht.1, ht.2⟩ u,
     fun j t ht => hC2.2.2.2 (Sum.inr ()) j t ⟨hSub2 ht.1, ht.2⟩⟩
  -- every HigherSRoomAt field from membership alone
  have hRoom : ∀ x ∈ tsupport (F0 : R3 → SphereL2),
      HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q δ x :=
    fun x hx => higherSRoomAt_of_mem_paramRoom hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q δ0 δ dG hδδ0 hδG hΩ0 hJac x (hMem x hx)
  exact higherSOutputConclusions_of_facts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 hg2 F0 hRoom

end Literal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation.higherSLift_inclusion_eq_movingQuotient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation.nativeHigherSHalf_negative_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation.higherSFormationContract_proof
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFormation.higherSUniformFormationContract_proof
