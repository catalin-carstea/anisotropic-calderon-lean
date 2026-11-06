import Calderon.ActualLowerUSFirstOutputLinearity
import Calderon.ActualLowerUSAdjointPresentation
import Calderon.ActualLowerUSLowerWordAdjoints
import Calderon.ActualHigherSLeadingBracketGain

/-! The exact first-output contraction and the complete physical J/P expansion.
The fixed Js is identified before the nonfinite physical output pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPPresentation
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation ActualHigherSFirstPhysicalCommutatorGraph
  ActualLowerUSFirstOutput ActualHigherSLeadingBracketGain
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "Pout" g2:max dr:max Ar:max p:max q:max =>
  nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q

/-- Exact literal ordered-weight contraction of the genuine physical P_j. -/
lemma nativeFirstOut_contracted (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (Pout g2 dr Ar p q) j F x = (referenceRadius dr Ar p L x)^2 •
      ∑ k : Fin 3, firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x) •
        sphereSobolevHalfToSphereL2L hO hD
          (EH k ((Tq dr Ar p q) x) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) := by
  unfold nativeFirstOut highFirstCoordinateCoefficient
  rw [highFirstCoordinateFactor_eq_contracted]
  simp only [smul_apply,sum_apply,map_smul,map_sum]

variable (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
local notation "J" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Js" => nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Word" => lowerQuadraticWord hO hD hF
local notation "WordStar" => lowerQuadraticWordAdjoint hO hD hF

/-- Exact physical J/P density used by the ordinary row. -/
def nativeJPCommutatorDensity (j : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪(Js U).val x,(Pout g2 dr Ar p q) j V x⟫_ℝ -
    ⟪U.val x,(Pout g2 dr Ar p q) j (J V) x⟫_ℝ

/-- The coefficient witness is global even when selected by its mass at x.
Its true reversed word adjoint is identified with fixed Js before pairing P. -/
lemma nativeJP_eq_lower_word_sum
    (c : (LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) → R3 → ℝ)
    (hc : ∀ ij, ContDiff ℝ ∞ (c ij)) (hJ : J = coreScalarCombination hO hD Word c hc)
    (j : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeJPCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q j U V x =
    ∑ ij, c ij x *
      (⟪(WordStar ij U).val x,(Pout g2 dr Ar p q) j V x⟫_ℝ -
        ⟪U.val x,(Pout g2 dr Ar p q) j (Word ij V) x⟫_ℝ) := by
  have hP : (Pout g2 dr Ar p q) j (J V) x = ∑ ij, c ij x • (Pout g2 dr Ar p q) j (Word ij V) x := by
    rw [hJ]
    exact nativeFirstOut_coreScalarCombination
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q j Word c hc V x
  have hS := nativeJs_inner_eq_presentation_sum hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
    Word WordStar (lowerQuadraticWord_inner_adjoint hO hD hF) c hc hJ U x ((Pout g2 dr Ar p q) j V x)
  unfold nativeJPCommutatorDensity
  rw [hS,hP]
  simp only [inner_sum,real_inner_smul_right,mul_sub,Finset.sum_sub_distrib]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSJPPresentation
