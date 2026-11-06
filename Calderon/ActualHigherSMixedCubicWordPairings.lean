import Calderon.ActualHigherSMixedCubicFirstOutputs
import Calderon.ActualHigherSActualCubicPairing

/-! Literal full3*3*207 mixed physical contraction, author source uncompiled.
Canonical own4511 first fields keep the original reverse minus. Every word and
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

private lemma weighted_bilinear_sum {ι κ E N : Type*}
    [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : E →L[ℝ] N →L[ℝ] ℝ) (theta : ι → ℝ) (lam : κ → ℝ)
    (A : ι → E) (F : κ → N) :
    P (∑ i : ι, theta i • A i) (∑ z : κ, lam z • F z) =
      ∑ i : ι, ∑ z : κ, (theta i*lam z)*P (A i) (F z) := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  ring

set_option diagnostics true in
/-- Complete first/word physical pairings from the original literal negative graphs.
Both graph hypotheses are discharged by the retained actual point owner in the public adapter. -/
theorem actual_first_pairings_eq_word_sums (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (Z T : Half)
    (hZ : JL Z = quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q x (UF F x))
    (hT : JL T = quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q x (UF F x)) :
    ⟪PF g2 dr Ar p q F x, KL Z⟫_ℝ =
      (∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (AH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (AL ((Tq dr Ar p q) x) (wordAtoms z).1
              (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))) ∧
    ⟪PR g2 dr Ar p q F x, KL T⟫_ℝ =
      -(∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (RH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (RL ((Tq dr Ar p q) x) (wordAtoms z).2
              (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))) := by
  let t := (Tq dr Ar p q) x
  let r := referenceRadius dr Ar p L x
  let U := UF F x
  let dU : Fin 3 → Hi := fun k => directionalFDeriv (coordinateDirection k) (UF F) x
  let theta : (Fin 3 × Fin 3) → ℝ := fun ki => r^2*firstCoordinateWeight g g2 L ki.1 ki.2 t
  let lam : ZeroWord → ℝ := WC g2 dr Ar p q x
  let A : (Fin 3 × Fin 3) → Half := fun ki => AH t (eAtom ki.2) (dU ki.1)
  let Bv : (Fin 3 × Fin 3) → Half := fun ki => RH t (eAtom ki.2) (dU ki.1)
  let Fn : ZeroWord → Neg := fun z => AL t (wordAtoms z).1 (AH t (wordAtoms z).2 U)
  let Gn : ZeroWord → Neg := fun z => RL t (wordAtoms z).2 (RH t (wordAtoms z).1 U)
  have hFirst := actual_first_outputs_eq_sums
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x
  have hPF : PF g2 dr Ar p q F x = KL (∑ ki : Fin 3 × Fin 3, theta ki • A ki) := by
    simpa only [theta, A, t, r, dU] using hFirst.1
  have hPR : PR g2 dr Ar p q F x = KL (-(∑ ki : Fin 3 × Fin 3, theta ki • Bv ki)) := by
    simpa only [theta, Bv, t, r, dU] using hFirst.2
  have hNZ : JL Z = ∑ z : ZeroWord, lam z • Fn z := by
    simpa only [quadraticZeroNegative, wordNegative, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, lam, Fn, t, U] using hZ
  have hNT : JL T = ∑ z : ZeroWord, lam z • Gn z := by
    simpa only [quadraticZeroReverseNegative, wordReverseNegative, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, lam, Gn, t, U] using hT
  have hForward : ⟪PF g2 dr Ar p q F x, KL Z⟫_ℝ =
      PL (∑ ki : Fin 3 × Fin 3, theta ki • A ki) (∑ z : ZeroWord, lam z • Fn z) :=
    (congrArg (fun v : SphereL2 => ⟪v, KL Z⟫_ℝ) hPF).trans
      ((ActualHigherSZeroAtomTransport.half_pairing_inner hO hD
        (∑ ki : Fin 3 × Fin 3, theta ki • A ki) Z).symm.trans
        (congrArg (PL (∑ ki : Fin 3 × Fin 3, theta ki • A ki)) hNZ))
  have hReverse : ⟪PR g2 dr Ar p q F x, KL T⟫_ℝ =
      PL (-(∑ ki : Fin 3 × Fin 3, theta ki • Bv ki)) (∑ z : ZeroWord, lam z • Gn z) :=
    (congrArg (fun v : SphereL2 => ⟪v, KL T⟫_ℝ) hPR).trans
      ((ActualHigherSZeroAtomTransport.half_pairing_inner hO hD
        (-(∑ ki : Fin 3 × Fin 3, theta ki • Bv ki)) T).symm.trans
        (congrArg (PL (-(∑ ki : Fin 3 × Fin 3, theta ki • Bv ki))) hNT))
  constructor
  · refine hForward.trans ?_
    have h := weighted_bilinear_sum PL theta lam A Fn
    simpa only [Fintype.sum_prod_type, theta, lam, A, Fn, t, r, U, dU,
      mixedWordScalar, ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h
  · refine hReverse.trans ?_
    have h := congrArg (fun v : ℝ => -v) (weighted_bilinear_sum PL theta lam Bv Gn)
    simpa only [map_neg, ContinuousLinearMap.neg_apply, Fintype.sum_prod_type,
      theta, lam, Bv, Gn, t, r, U, dU, mixedWordScalar,
      ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicPhysicalExpansion
