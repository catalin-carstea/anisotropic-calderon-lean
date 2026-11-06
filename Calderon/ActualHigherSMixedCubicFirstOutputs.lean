import Calderon.ActualHigherSActualCubicPairing

/-! Literal full 3*3*207 mixed physical contraction.
The canonical first fields keep the original reverse minus. Every word and
coefficient order is retained. No output angular restriction or analytic callback. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicPhysicalExpansion
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ActualHigherSActualCubicPairing PrincipalCommutator
  ReferenceDensityBounds ActualHigherSLeadingBracketGain
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WC" => actualWordCoefficient g L
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow sphereSobolevInclusionL
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh actualZ2Half actualT2Half cubicAtomForm

/-- The complete forward coordinate contraction at an arbitrary original High input. -/
lemma actual_first_coordinate_apply_eq_sum
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (k : Fin 3) (v : Hi) :
    PH g2 dr Ar p q x k v = ∑ i : Fin 3,
      ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)) •
        AH ((Tq dr Ar p q) x) (eAtom i) v := by
  let t := (Tq dr Ar p q) x
  let r := referenceRadius dr Ar p L x
  have hAH (i : Fin 3) : AH t (eAtom i) = EH i t := by
    simp only [ActualHigherSQuadraticZeroWords.eAtom,
      ActualHigherSQuadraticZeroWords.atomHigh]
  have h : PH g2 dr Ar p q x k = r^2 •
      (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • EH i t) :=
    (ActualPPLowerRemainder.actual_first_coordinate_contractions
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k).1
  have hSum :
      (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • EH i t) (v) =
        ∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • EH i t (v) :=
    _root_.sum_apply Finset.univ
      (fun i : Fin 3 => firstCoordinateWeight g g2 L k i t • EH i t) (v)
  calc
    PH g2 dr Ar p q x k (v) = r^2 •
        ((∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • EH i t) (v)) :=
      congrArg (fun T : Hi →L[ℝ] Half => T (v)) h
    _ = r^2 • (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • EH i t (v)) :=
      congrArg (fun z : Half => r^2 • z) hSum
    _ = ∑ i : Fin 3, r^2 • (firstCoordinateWeight g g2 L k i t • EH i t (v)) := by
      rw [Finset.smul_sum]
    _ = ∑ i : Fin 3, (r^2*firstCoordinateWeight g g2 L k i t) • AH t (eAtom i) v := by
      apply Finset.sum_congr rfl
      intro i _
      change r^2 • (firstCoordinateWeight g g2 L k i t • EH i t (v)) =
        (r^2*firstCoordinateWeight g g2 L k i t) • AH t (eAtom i) (v)
      have hValue : EH i t (v) = AH t (eAtom i) (v) :=
        congrArg (fun T : Hi →L[ℝ] Half => T (v)) (hAH i).symm
      exact (smul_smul (r^2) (firstCoordinateWeight g g2 L k i t) (EH i t (v))).trans
        (congrArg (fun z : Half => (r^2*firstCoordinateWeight g g2 L k i t) • z) hValue)

/-- The complete genuine negative reverse coordinate contraction at an arbitrary High input. -/
lemma actual_reverse_first_coordinate_apply_eq_neg_sum
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (k : Fin 3) (v : Hi) :
    DH g2 dr Ar p q x k v = -(∑ i : Fin 3,
      ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)) •
        RH ((Tq dr Ar p q) x) (eAtom i) v) := by
  let t := (Tq dr Ar p q) x
  let r := referenceRadius dr Ar p L x
  have hRH (i : Fin 3) : RH t (eAtom i) = BH i t := by
    simp only [ActualHigherSQuadraticZeroWords.eAtom,
      ActualHigherSQuadraticZeroWords.atomReverseHigh]
  have h : DH g2 dr Ar p q x k = (-r^2) •
      (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • BH i t) :=
    (ActualPPLowerRemainder.actual_first_coordinate_contractions
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k).2.2.1
  have hSum :
      (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • BH i t) (v) =
        ∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • BH i t (v) :=
    _root_.sum_apply Finset.univ
      (fun i : Fin 3 => firstCoordinateWeight g g2 L k i t • BH i t) (v)
  calc
    DH g2 dr Ar p q x k (v) = (-r^2) •
        ((∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • BH i t) (v)) :=
      congrArg (fun T : Hi →L[ℝ] Half => T (v)) h
    _ = (-r^2) • (∑ i : Fin 3, firstCoordinateWeight g g2 L k i t • BH i t (v)) :=
      congrArg (fun z : Half => (-r^2) • z) hSum
    _ = ∑ i : Fin 3, (-r^2) • (firstCoordinateWeight g g2 L k i t • BH i t (v)) := by
      rw [Finset.smul_sum]
    _ = ∑ i : Fin 3, -((r^2*firstCoordinateWeight g g2 L k i t) • RH t (eAtom i) v) := by
      apply Finset.sum_congr rfl
      intro i _
      change (-r^2) • (firstCoordinateWeight g g2 L k i t • BH i t (v)) =
        -((r^2*firstCoordinateWeight g g2 L k i t) • RH t (eAtom i) (v))
      have hValue : BH i t (v) = RH t (eAtom i) (v) :=
        congrArg (fun T : Hi →L[ℝ] Half => T (v)) (hRH i).symm
      exact (neg_smul (r^2) (firstCoordinateWeight g g2 L k i t • BH i t (v))).trans
        (congrArg (fun z : Half => -z)
          ((smul_smul (r^2) (firstCoordinateWeight g g2 L k i t) (BH i t (v))).trans
            (congrArg (fun z : Half => (r^2*firstCoordinateWeight g g2 L k i t) • z) hValue)))
    _ = -(∑ i : Fin 3, (r^2*firstCoordinateWeight g g2 L k i t) • RH t (eAtom i) v) := by
      rw [Finset.sum_neg_distrib]

/-- The complete forward physical output as the original nine-term sum. -/
lemma actual_first_output_eq_sum
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PF g2 dr Ar p q F x = KL (∑ ki : Fin 3 × Fin 3,
      ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L ki.1 ki.2 ((Tq dr Ar p q) x)) •
        AH ((Tq dr Ar p q) x) (eAtom ki.2)
          (directionalFDeriv (coordinateDirection ki.1) (UF F) x)) := by
  unfold ActualPPLowerRemainder.actualPPFirstOut
  change KL (∑ k : Fin 3, PH g2 dr Ar p q x k
    (directionalFDeriv (coordinateDirection k) (UF F) x)) = _
  apply congrArg KL
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun k _ => actual_first_coordinate_apply_eq_sum
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k
      (directionalFDeriv (coordinateDirection k) (UF F) x))

/-- The complete reverse physical output, retaining the negative of all nine terms. -/
lemma actual_reverse_first_output_eq_neg_sum
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PR g2 dr Ar p q F x = KL (-(∑ ki : Fin 3 × Fin 3,
      ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L ki.1 ki.2 ((Tq dr Ar p q) x)) •
        RH ((Tq dr Ar p q) x) (eAtom ki.2)
          (directionalFDeriv (coordinateDirection ki.1) (UF F) x))) := by
  unfold ActualPPLowerRemainder.actualPPReverseFirstOut
  change KL (∑ k : Fin 3, DH g2 dr Ar p q x k
    (directionalFDeriv (coordinateDirection k) (UF F) x)) = _
  apply congrArg KL
  rw [Fintype.sum_prod_type]
  calc
    (∑ k : Fin 3, DH g2 dr Ar p q x k
      (directionalFDeriv (coordinateDirection k) (UF F) x)) =
        ∑ k : Fin 3, -(∑ i : Fin 3,
          ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)) •
            RH ((Tq dr Ar p q) x) (eAtom i)
              (directionalFDeriv (coordinateDirection k) (UF F) x)) :=
      Finset.sum_congr rfl (fun k _ => actual_reverse_first_coordinate_apply_eq_neg_sum
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k
          (directionalFDeriv (coordinateDirection k) (UF F) x))
    _ = -(∑ k : Fin 3, ∑ i : Fin 3,
          ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)) •
            RH ((Tq dr Ar p q) x) (eAtom i)
              (directionalFDeriv (coordinateDirection k) (UF F) x)) := by
      rw [Finset.sum_neg_distrib]

set_option diagnostics true in
/-- Complete original forward and genuine negative reverse first-output sums.
This statement and proof have no endpoint Room, hreg or data context. -/
theorem actual_first_outputs_eq_sums (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PF g2 dr Ar p q F x = KL (∑ ki : Fin 3 × Fin 3,
          ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L ki.1 ki.2 ((Tq dr Ar p q) x)) •
            AH ((Tq dr Ar p q) x) (eAtom ki.2)
              (directionalFDeriv (coordinateDirection ki.1) (UF F) x)) ∧
    PR g2 dr Ar p q F x = KL (-(∑ ki : Fin 3 × Fin 3,
          ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L ki.1 ki.2 ((Tq dr Ar p q) x)) •
            RH ((Tq dr Ar p q) x) (eAtom ki.2)
              (directionalFDeriv (coordinateDirection ki.1) (UF F) x))) := by
  exact ⟨actual_first_output_eq_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x,
    actual_reverse_first_output_eq_neg_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicPhysicalExpansion
