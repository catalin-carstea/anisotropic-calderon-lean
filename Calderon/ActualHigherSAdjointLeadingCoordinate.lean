import Calderon.ActualHigherSLeadingBracketGain
import Calderon.ActualHigherSAdjointCoefficientExtraction
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointLeadingCoordinate
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualHigherSLeadingBracketGain
  ActualHigherSCoefficientExtraction ActualHigherSAdjointCoefficientExtraction
  SmoothMetricFrame ConformalDepth ActualFiniteHarmonicCore
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
theorem weighted_adjoint_contraction (r : ℝ) (X : Fin 3 → ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (E : Fin 3 → V) :
    (∑ m : Fin 3, X m • (-(r^2 • (∑ j : Fin 3, Q m j • E j)+r^2 • (∑ i : Fin 3, Q i m • E i)))) =
      (-r^2) • (∑ a : Fin 3, (∑ m : Fin 3, X m*(Q m a+Q a m)) • E a) := by
  have hrow (m : Fin 3) : -(r^2 • (∑ j : Fin 3, Q m j • E j)+r^2 • (∑ i : Fin 3, Q i m • E i)) =
      (-r^2) • ((∑ j : Fin 3, Q m j • E j)+(∑ i : Fin 3, Q i m • E i)) := by
    simp only [smul_add,neg_smul,neg_add]
  calc
    _ = (-r^2) • (∑ m : Fin 3, X m • ((∑ j : Fin 3, Q m j • E j)+(∑ i : Fin 3, Q i m • E i))) := by
      simp_rw [hrow]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact smul_comm _ _ _
    _ = _ := congrArg (fun z : V => (-r^2) • z) (firstFactor_contraction X Q E)
end Algebra

/-- The original actual endpoint coefficients specialize only the checked scalar module algebra. -/
theorem adjointFirstCoordinateCoefficient_contracted (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (E : Fin 3 → Half →L[ℝ] Neg) (X : Fin 3 → R3) (l : Fin 3) :
    firstCoordinateCoefficient (fun m => adjointFirstFrameCoefficient r Q E m) X l =
      (-r^2) • (∑ a : Fin 3, (∑ m : Fin 3, X m l*(Q m a+Q a m)) • E a) := by
  exact weighted_adjoint_contraction r (fun m => X m l) Q E

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
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "BF" => higherSAdjointFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "ADJ" => ActualHigherSAdjointFormation.higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BR" => orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem reverseEHigh_eq_ordered (i : Fin 3) (t : Tpar) :
    ActualGeneratorEPairedGainedEndpoints.reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t =
      orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t := rfl

theorem reverseELow_eq_ordered (i : Fin 3) (t : Tpar) :
    ActualGeneratorEPairedGainedEndpoints.reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t =
      orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t := rfl

/-- Exactly the standard coordinate conversion of the actual extracted full-adjoint frame coefficient. -/
def actualAdjointFirstCoordinateCoefficient (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (q : ℝ) (x : R3) (l : Fin 3) : Half →L[ℝ] Neg :=
  firstCoordinateCoefficient (BF g2 dr Ar p q x) (referenceMetricGramFrame g L (q,x)) l

/-- The true complete adjoint first coefficient equals the ordered reverse leading factor. -/
theorem actualAdjointFirstCoordinateCoefficient_eq_contracted
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (l : Fin 3) :
    actualAdjointFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x l =
      (-(referenceRadius dr Ar p L x)^2) • BR g2 l ((Tq dr Ar p q) x) := by
  unfold actualAdjointFirstCoordinateCoefficient higherSAdjointFirstFrameCoefficient
  rw [adjointFirstCoordinateCoefficient_contracted]
  rfl

attribute [local irreducible] ActualHigherSAdjointFormation.higherSAdjointHalf
  higherSAdjointZeroCoefficient higherSAdjointFirstFrameCoefficient
  sphereSobolevInclusionL orderedReverseHigh orderedReverseLow

/-- Complete original adjoint coordinate identity, with the existing full zero coefficient retained. -/
theorem actual_higherS_adjoint_coordinate_coefficient
    (hreg : FixedDirichletRegularity) (d0 : ℝ) (W : CoeffRoom d0)
    (d : ℝ) (Cm : CRoom hreg d0 W d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom d) (x : R3) :
    JL (ADJ hreg d0 W g2 dr Ar p hdr hAr q F x) =
      (∑ l : Fin 3, ((-(referenceRadius dr Ar p L x)^2) • BR g2 l ((Tq dr Ar p q) x))
        (IH (fderiv ℝ (UF F) x (ReferenceDensityBounds.coordinateDirection l)))) +
      CZ g2 dr Ar p q x (UF F x) := by
  have hf := actual_higherS_adjoint_frame_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 W d Cm g2 dr Ar p hdr hAr q F hT x
  have hc := frame_to_coordinate (BF g2 dr Ar p q x) (referenceMetricGramFrame g L (q,x)) (UF F) x
  have he := hf.trans (congrArg (fun v : Neg => v+CZ g2 dr Ar p q x (UF F x)) hc)
  have hcoef := actualAdjointFirstCoordinateCoefficient_eq_contracted g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 dr Ar p q x
  dsimp only [actualAdjointFirstCoordinateCoefficient] at hcoef
  simpa only [hcoef] using he

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointLeadingCoordinate
