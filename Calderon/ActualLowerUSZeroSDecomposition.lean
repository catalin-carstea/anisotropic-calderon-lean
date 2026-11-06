import Calderon.ActualHigherSZeroCoefficientJets

/-!
Exact native S zero grouping into one-factor and two-factor angular words.
Every profile-log, connection, drift and ordered principal coefficient is retained.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroSDecomposition
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Small vector data for one genuine zero-coefficient application. -/
private structure ZeroRowData where
  r : ℝ
  Q : Fin 3 → Fin 3 → ℝ
  b : Fin 3 → ℝ
  f : Fin 3 → ℝ
  gamma : Fin 3 → Fin 3 → Fin 3 → ℝ
  e : Fin 3 → Half
  de : Fin 3 → Fin 3 → Half
  o : Fin 3 → Half
  n : Half
  a : Fin 3 → Half
  el : Fin 3 → Half →L[ℝ] Neg
  ol : Fin 3 → Half →L[ℝ] Neg
  al : Fin 3 → Half →L[ℝ] Neg
  nl : Half →L[ℝ] Neg

private def rawZeroRow (d : ZeroRowData) : Neg :=
  ((d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (JL (d.de i j)+(d.ol i+d.f i • d.nl) (d.e j)+
        d.el i (d.o j+d.f j • d.n)+d.f i • JL (d.e j)-
        ∑ k : Fin 3, d.gamma i k j • JL (d.e k)))+
    d.r^2 • (∑ i : Fin 3, d.b i • JL (d.e i)))+
    d.r • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (d.al i (d.e j)+d.el i (d.a j))))+
    d.r^3 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j • d.el i (d.e j))

private def groupedZeroRow (d : ZeroRowData) : Neg :=
  (d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (JL (d.de i j)+d.f i • JL (d.e j)-
        ∑ k : Fin 3, d.gamma i k j • JL (d.e k)))+
    d.r^2 • (∑ i : Fin 3, d.b i • JL (d.e i)))+
    d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (d.ol i (d.e j)+d.el i (d.o j)))+
    d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (d.f i • d.nl (d.e j)+d.f j • d.el i d.n))+
    d.r • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
      (d.al i (d.e j)+d.el i (d.a j)))+
    d.r^3 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j • d.el i (d.e j))

private theorem rawZeroRow_eq_grouped (d : ZeroRowData) : rawZeroRow d = groupedZeroRow d := by
  simp only [rawZeroRow,groupedZeroRow,Fin.sum_univ_three,add_apply,smul_apply,map_add,map_smul]
  module

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)

local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "RR" => referenceRadius dr Ar p L
local notation "EH" j:max x:max => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j (Tq x)
local notation "EL" j:max x:max => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j (Tq x)
local notation "QQ" i:max j:max x:max => referenceDensityPrincipalFrameCoefficient g g2 L q x i j
local notation "FF" i:max x:max => referenceRadiusHorizontalLogDerivative g L q RR x i
local notation "XX" i:max x:max => referenceMetricGramFrame g L (q,x) i
local notation "GG" i:max k:max j:max x:max => referenceFrameConnectionCoefficient g L q x (XX i x) k j
local notation "OH" i:max x:max => referenceHighHorizontalAngularL g L q x i
local notation "OL" i:max x:max => referenceLowerHorizontalAngularL g L q x i

/-- The differentiated E, extra log scalar, connection scalar and drift groups. -/
def lowerSZeroLinearGroup (x : R3) : Hi →L[ℝ] Neg :=
  (RR x)^2 • (∑ i : Fin 3, ∑ j : Fin 3, QQ i j x •
    (ContinuousLinearMap.comp JL (fderiv ℝ (fun y => EH j y) x (XX i x)) +
      FF i x • ContinuousLinearMap.comp JL (EH j x) -
      ∑ k : Fin 3, GG i k j x • ContinuousLinearMap.comp JL (EH k x))) +
  (RR x)^2 • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,x) •
    ContinuousLinearMap.comp JL (EH i x))

/-- Both original ordered connection/E products. -/
def lowerSZeroConnectionGroup (x : R3) : Hi →L[ℝ] Neg :=
  (RR x)^2 • (∑ i : Fin 3, ∑ j : Fin 3, QQ i j x •
    ((OL i x).comp (EH j x) + (EL i x).comp (OH j x)))

/-- Both original degree/E products and their distinct profile-log coefficients. -/
def lowerSZeroDegreeGroup (x : R3) : Hi →L[ℝ] Neg :=
  (RR x)^2 • (∑ i : Fin 3, ∑ j : Fin 3, QQ i j x •
    (FF i x • (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp (EH j x) +
      FF j x • (EL i x).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ))))

/-- Angular-coordinate transpose/E in the original order. -/
def lowerSZeroAngularGroup (x : R3) : Hi →L[ℝ] Neg :=
  RR x • (∑ i : Fin 3, ∑ j : Fin 3, QQ i j x •
    ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (EH j x) +
      (EL i x).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))

/-- The complete ordered quadratic E/E group. -/
def lowerSZeroDoubleGroup (x : R3) : Hi →L[ℝ] Neg :=
  (RR x)^3 • (∑ i : Fin 3, ∑ j : Fin 3, QQ i j x • (EL i x).comp (EH j x))

private def actualZeroRowData (x : R3) (u : Hi) : ZeroRowData where
  r := RR x
  Q := fun i j => QQ i j x
  b := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  f := fun i => FF i x
  gamma := fun i k j => GG i k j x
  e := fun j => (EH j x) u
  de := fun i j => (fderiv ℝ (fun y => EH j y) x (XX i x)) u
  o := fun j => (OH j x) u
  n := sphereSobolevShiftedDegreeL (3/2 : ℝ) u
  a := fun j => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u
  el := fun j => EL j x
  ol := fun i => OL i x
  al := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)
  nl := sphereSobolevShiftedDegreeL (1/2 : ℝ)

private theorem canonicalZeroCoefficient_actual_projection (x : R3) (u : Hi) :
    ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x u =
      rawZeroRow (actualZeroRowData
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x u) := by
  have hProfile (j : Fin 3) :
      ActualHigherSCoefficientExtraction.profileHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q j =
      (fun y => EH j y) := rfl
  simp only [ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient,
    ActualHigherSZeroCoefficientJets.zeroCoefficientWith,
    ActualHigherSCoefficientExtraction.zeroCoefficient,
    ActualHigherSCoefficientExtraction.secondZeroRow,
    ActualHigherSCoefficientExtraction.weightedLowerZero,
    ActualHigherSCoefficientExtraction.weightedHighZero,
    hProfile,
    rawZeroRow,actualZeroRowData,add_apply,sub_apply,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,map_add,map_smul]

private theorem five_groups_actual_projection (x : R3) (u : Hi) :
    (lowerSZeroLinearGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroConnectionGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroDegreeGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroAngularGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroDoubleGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x) u =
      groupedZeroRow (actualZeroRowData
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x u) := by
  simp only [lowerSZeroLinearGroup,lowerSZeroConnectionGroup,lowerSZeroDegreeGroup,
    lowerSZeroAngularGroup,lowerSZeroDoubleGroup,groupedZeroRow,actualZeroRowData,
    add_apply,sub_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply]

/-- Literal full canonical zero coefficient, with no symmetry premise, dropped
scalar row, or replacement physical response. -/
theorem canonicalZeroCoefficient_eq_lower_groups (x : R3) :
    ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x =
    lowerSZeroLinearGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroConnectionGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroDegreeGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroAngularGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x +
    lowerSZeroDoubleGroup g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x := by
  apply ContinuousLinearMap.ext
  intro u
  exact (canonicalZeroCoefficient_actual_projection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x u).trans
    ((rawZeroRow_eq_grouped _).trans (five_groups_actual_projection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x u).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroSDecomposition
