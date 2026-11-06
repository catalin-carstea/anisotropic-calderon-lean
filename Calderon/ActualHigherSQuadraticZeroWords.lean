import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualHigherSAdjointCoefficientExtraction
import Calderon.ActualHigherSZeroParameterFactors
import Calderon.ActualRaisingEHighGraph

/-! Complete finite angular-word definitions, successor v002. UNCOMPILED.
No all-atom gain producer, coefficient equality, physical realization or bound is asserted here.
Exact before-source expansion and contract are archived with this package. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroWords
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  SmoothMetricFrame MovingFrameConnection ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- The actual 16 forward angular atoms: three E, nine rotations and degree, three raising. -/
abbrev ZeroAtom := (Fin 3) ⊕ (Generator ⊕ Fin 3)
/-- Two rotation placements and five remaining word placements; 23 kinds. -/
abbrev ZeroWordKind := (Fin 3 × Fin 3) ⊕ ((Fin 3 × Fin 3) ⊕ Fin 5)
/-- The 207 original ordered length-two summands; no index symmetry is imposed. -/
abbrev ZeroWord := (Fin 3 × Fin 3) × ZeroWordKind

def degreeAtom : ZeroAtom := Sum.inr (Sum.inl (Sum.inr ()))
def eAtom (i : Fin 3) : ZeroAtom := Sum.inl i
def rotationAtom (a b : Fin 3) : ZeroAtom := Sum.inr (Sum.inl (Sum.inl (a,b)))
def raisingAtom (i : Fin 3) : ZeroAtom := Sum.inr (Sum.inr i)

def wordAtoms (w : ZeroWord) : ZeroAtom × ZeroAtom :=
  let i := w.1.1
  let j := w.1.2
  match w.2 with
  | Sum.inl ab => (rotationAtom ab.1 ab.2, eAtom j)
  | Sum.inr (Sum.inl ab) => (eAtom i, rotationAtom ab.1 ab.2)
  | Sum.inr (Sum.inr m) =>
    if m = 0 then (degreeAtom, eAtom j) else
    if m = 1 then (eAtom i, degreeAtom) else
    if m = 2 then (raisingAtom i, eAtom j) else
    if m = 3 then (eAtom i, raisingAtom j) else (eAtom i, eAtom j)

/-- Literal scalar coefficient: r²Γ/2, r²f, r, or r³, always with original Q_ij. -/
def wordCoefficient (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ZeroWord) : ℝ :=
  let i := w.1.1
  let j := w.1.2
  match w.2 with
  | Sum.inl ab => (r^2/2) * Q i j * Γ i ab.1 ab.2
  | Sum.inr (Sum.inl ab) => (r^2/2) * Q i j * Γ j ab.1 ab.2
  | Sum.inr (Sum.inr m) =>
    if m = 0 then r^2 * Q i j * f i else
    if m = 1 then r^2 * Q i j * f j else
    if m = 2 then r * Q i j else
    if m = 3 then r * Q i j else r^3 * Q i j

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

def atomHigh (t : Tpar) : ZeroAtom → Hi →L[ℝ] Half
  | Sum.inl i => EH i t
  | Sum.inr (Sum.inl V) => generatorHigh V
  | Sum.inr (Sum.inr i) => raisingHigh hF hO hD i

def atomLow (t : Tpar) : ZeroAtom → Half →L[ℝ] Neg
  | Sum.inl i => EL i t
  | Sum.inr (Sum.inl V) => generatorLow V
  | Sum.inr (Sum.inr i) => raisingLow hF hO hD i

def atomReverseHigh (t : Tpar) : ZeroAtom → Hi →L[ℝ] Half
  | Sum.inl i => BH i t
  | Sum.inr (Sum.inl V) => generatorSharpHigh V
  | Sum.inr (Sum.inr i) => loweringHigh hF hO hD i

def atomReverseLow (t : Tpar) : ZeroAtom → Half →L[ℝ] Neg
  | Sum.inl i => BL i t
  | Sum.inr (Sum.inl V) => generatorSharpLow V
  | Sum.inr (Sum.inr i) => loweringLow hF hO hD i

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- A forward word is low(first) after high(second), exactly at Hi→Neg. -/
def wordNegative (t : Tpar) (w : ZeroWord) : Hi →L[ℝ] Neg :=
  (AL t (wordAtoms w).1).comp (AH t (wordAtoms w).2)
/-- The genuine reverse word reverses BOTH atom order and adjoint partners. -/
def wordReverseNegative (t : Tpar) (w : ZeroWord) : Hi →L[ℝ] Neg :=
  (RL t (wordAtoms w).2).comp (RH t (wordAtoms w).1)

def actualWordCoefficient (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (w : ZeroWord) : ℝ :=
  wordCoefficient (referenceRadius dr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
    (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b ((Tq dr Ar p q) x)) w

local notation "WC" => actualWordCoefficient g L
local notation "WN" => wordNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WR" => wordReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The fully finite angular-order-two negative family; physical realization still needs its chosen lifts. -/
def quadraticZeroNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Neg :=
  ∑ w : ZeroWord, WC g2 dr Ar p q x w • WN ((Tq dr Ar p q) x) w
/-- Exactly the SAME scalar coefficients, with literal reversed genuine adjoint words. -/
def quadraticZeroReverseNegative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Neg :=
  ∑ w : ZeroWord, WC g2 dr Ar p q x w • WR ((Tq dr Ar p q) x) w

/-- Chosen Hi lifts belong only to original finite input; no lift of a gained output appears. -/
def wordHalf (t : Tpar) (V : ZeroAtom → Hi) (z : ZeroWord) : Half :=
  AH t (wordAtoms z).1 (V (wordAtoms z).2)
/-- Literal reversed word: reverse(second) acts on the chosen reverse(first) lift. -/
def wordReverseHalf (t : Tpar) (v : ZeroAtom → Hi) (z : ZeroWord) : Half :=
  RH t (wordAtoms z).2 (v (wordAtoms z).1)

def quadraticZeroHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (V : ZeroAtom → Hi) : Half :=
  ∑ z : ZeroWord, WC g2 dr Ar p q x z •
    wordHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x) V z

def quadraticZeroReverseHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (v : ZeroAtom → Hi) : Half :=
  ∑ z : ZeroWord, WC g2 dr Ar p q x z •
    wordReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x) v z

lemma card_zeroAtom : Fintype.card ZeroAtom = 16 := by decide
lemma card_zeroWord : Fintype.card ZeroWord = 207 := by
  norm_num [ZeroWord, ZeroWordKind]

section FiniteWordExpansion
variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Literal seven-family expansion, with all original ordered indices. -/
def sevenWordRows (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (W : ZeroAtom → ZeroAtom → E) : E :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ((∑ a : Fin 3, ∑ b : Fin 3, ((r^2/2)*Q i j*Γ i a b) • W (rotationAtom a b) (eAtom j)) +
    (∑ a : Fin 3, ∑ b : Fin 3, ((r^2/2)*Q i j*Γ j a b) • W (eAtom i) (rotationAtom a b)) +
    (r^2*Q i j*f i) • W degreeAtom (eAtom j) +
    (r^2*Q i j*f j) • W (eAtom i) degreeAtom +
    (r*Q i j) • W (raisingAtom i) (eAtom j) +
    (r*Q i j) • W (eAtom i) (raisingAtom j) +
    (r^3*Q i j) • W (eAtom i) (eAtom j))

lemma sum_wordCoefficient_smul_eq_seven_rows (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (f : Fin 3 → ℝ) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (W : ZeroAtom → ZeroAtom → E) :
    (∑ z : ZeroWord, wordCoefficient r Q f Γ z • W (wordAtoms z).1 (wordAtoms z).2) =
      sevenWordRows r Q f Γ W := by
  simp only [sevenWordRows, Fintype.sum_prod_type, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [wordCoefficient, wordAtoms, Fin.sum_univ_succ, add_assoc]

end FiniteWordExpansion

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL atomHigh atomLow atomReverseHigh atomReverseLow
  wordNegative wordReverseNegative actualWordCoefficient

lemma quadraticZeroNegative_eq_seven_rows (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x =
      sevenWordRows (referenceRadius dr Ar p L x)
        (referenceDensityPrincipalFrameCoefficient g g2 L q x)
        (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
        (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection
          g L i a b ((Tq dr Ar p q) x))
        (fun a b => (AL ((Tq dr Ar p q) x) a).comp (AH ((Tq dr Ar p q) x) b)) := by
  simpa only [quadraticZeroNegative, actualWordCoefficient, wordNegative] using
    sum_wordCoefficient_smul_eq_seven_rows (E := Hi →L[ℝ] Neg)
      (referenceRadius dr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
      (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection
        g L i a b ((Tq dr Ar p q) x))
      (fun a b => (AL ((Tq dr Ar p q) x) a).comp (AH ((Tq dr Ar p q) x) b))

lemma quadraticZeroReverseNegative_eq_seven_rows (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x =
      sevenWordRows (referenceRadius dr Ar p L x)
        (referenceDensityPrincipalFrameCoefficient g g2 L q x)
        (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
        (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection
          g L i a b ((Tq dr Ar p q) x))
        (fun a b => (RL ((Tq dr Ar p q) x) b).comp (RH ((Tq dr Ar p q) x) a)) := by
  simpa only [quadraticZeroReverseNegative, actualWordCoefficient, wordReverseNegative] using
    sum_wordCoefficient_smul_eq_seven_rows (E := Hi →L[ℝ] Neg)
      (referenceRadius dr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
      (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection
        g L i a b ((Tq dr Ar p q) x))
      (fun a b => (RL ((Tq dr Ar p q) x) b).comp (RH ((Tq dr Ar p q) x) a))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroWords
