import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualHigherSIntegratedPairing
import Calderon.ActualHigherSScalarCommutatorForm
import Calderon.ActualHigherSAdjointCoefficientExtraction
import Calderon.ActualHigherSZeroParameterFactors
/-! Explicit linear zero-base high operators.
These definitions are explicit derivative/coefficient/density rows, never residuals. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZero
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ConformalDepth PrincipalCommutator ActualHigherSScalarCommutatorForm
open SmoothMetricFrame MovingFrameConnection
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
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def normalizedSecondCoefficientDerivative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (i j k : Fin 3) (x : R3) : ℝ :=
  ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q k
    (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
    referenceDensityFamily g L (q,x)

def linearZeroHigh (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Half :=
  let R := referenceRadius dr Ar p L
  let t := (Tq dr Ar p q) x
  let X := referenceMetricGramFrame g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  (R x)^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
    (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x (X i)+f i • EH j t-
      ∑ k : Fin 3,Gamma i k j • EH k t))+
  (R x)^2 • (∑ i : Fin 3,normalizedSecondDriftFrameJoint g g2 L i (q,x) • EH i t)

def linearAdjointZeroHigh (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Hi →L[ℝ] Half :=
  let R := referenceRadius dr Ar p L
  let t := (Tq dr Ar p q) x
  let X := referenceMetricGramFrame g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  ((R x)^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
    (-(fderiv ℝ (fun y => BH i ((Tq dr Ar p q) y)) x (X j))+f i • BH j t-
      ∑ k : Fin 3,Gamma i k j • BH k t))-
    ∑ i : Fin 3,∑ j : Fin 3,
      (normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x • BH j t+
       normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x • BH i t))+
  (R x)^2 • (∑ i : Fin 3,normalizedSecondDriftFrameJoint g g2 L i (q,x) • BH i t)
local notation "Z1" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0


/-- Original normalized derivative coefficient is globally smooth for an actual
positive radius; divide only by the original positive reference density. -/
lemma contDiff_normalizedSecondCoefficientDerivative (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (i j k : Fin 3) :
    ContDiff ℝ ∞ (normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j k) := by
  have ha := ActualHigherSSecondAdjoint.contDiff_secondCoefficient
    g g2 hg hg2 L q dr Ar p hdr hAr i j
  have hd := ActualHigherSSecondAdjoint.contDiff_densityDerivativeCoefficient
    g hg L q k (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) ha
  unfold normalizedSecondCoefficientDerivative
  have hmu : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hquot : ContDiff ℝ ∞ (fun y : R3 =>
      ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q k
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) y /
        referenceDensityFamily g L (q,y)) :=
    hd.div hmu (fun y => (referenceDensityFamily_pos g hg L (q,y)).ne')
  exact hquot

private def forwardLinearRows {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ) (f b : Fin 3 → R3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (E : Fin 3 → R3 → V) (D : Fin 3 → Fin 3 → R3 → V) (y : R3) : V :=
  (R y)^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j y •
    (D i j y+f i y • E j y-∑ k : Fin 3,Gamma i k j y • E k y))+
  (R y)^2 • (∑ i : Fin 3,b i y • E i y)

private def reverseLinearRows {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ) (f b : Fin 3 → R3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (E : Fin 3 → R3 → V) (D : Fin 3 → Fin 3 → R3 → V)
    (d1 d2 : Fin 3 → Fin 3 → R3 → ℝ) (y : R3) : V :=
  ((R y)^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j y •
    (-D i j y+f i y • E j y-∑ k : Fin 3,Gamma i k j y • E k y))-
    ∑ i : Fin 3,∑ j : Fin 3,(d1 i j y • E j y+d2 i j y • E i y))+
  (R y)^2 • (∑ i : Fin 3,b i y • E i y)

private lemma contDiffAt_forwardLinearRows {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ) (f b : Fin 3 → R3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (E : Fin 3 → R3 → V) (D : Fin 3 → Fin 3 → R3 → V) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (hQ : ∀ i j,ContDiffAt ℝ ∞ (Q i j) x)
    (hf : ∀ i,ContDiffAt ℝ ∞ (f i) x) (hb : ∀ i,ContDiffAt ℝ ∞ (b i) x)
    (hG : ∀ i k j,ContDiffAt ℝ ∞ (Gamma i k j) x)
    (hE : ∀ i,ContDiffAt ℝ ∞ (E i) x) (hD : ∀ i j,ContDiffAt ℝ ∞ (D i j) x) :
    ContDiffAt ℝ ∞ (forwardLinearRows R Q f b Gamma E D) x := by
  have hrow (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => D i j y+f i y • E j y-∑ k : Fin 3,Gamma i k j y • E k y) x :=
    ((hD i j).add ((hf i).smul (hE j))).sub
      (ContDiffAt.sum (fun k _ => (hG i k j).smul (hE k)))
  exact ((hR.pow 2).smul (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    (hQ i j).smul (hrow i j))))).add
    ((hR.pow 2).smul (ContDiffAt.sum (fun i _ => (hb i).smul (hE i))))

private lemma contDiffAt_reverseLinearRows {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ) (f b : Fin 3 → R3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (E : Fin 3 → R3 → V) (D : Fin 3 → Fin 3 → R3 → V)
    (d1 d2 : Fin 3 → Fin 3 → R3 → ℝ) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (hQ : ∀ i j,ContDiffAt ℝ ∞ (Q i j) x)
    (hf : ∀ i,ContDiffAt ℝ ∞ (f i) x) (hb : ∀ i,ContDiffAt ℝ ∞ (b i) x)
    (hG : ∀ i k j,ContDiffAt ℝ ∞ (Gamma i k j) x)
    (hE : ∀ i,ContDiffAt ℝ ∞ (E i) x) (hD : ∀ i j,ContDiffAt ℝ ∞ (D i j) x)
    (hd1 : ∀ i j,ContDiffAt ℝ ∞ (d1 i j) x) (hd2 : ∀ i j,ContDiffAt ℝ ∞ (d2 i j) x) :
    ContDiffAt ℝ ∞ (reverseLinearRows R Q f b Gamma E D d1 d2) x := by
  have hrow (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => -D i j y+f i y • E j y-∑ k : Fin 3,Gamma i k j y • E k y) x :=
    ((hD i j).neg.add ((hf i).smul (hE j))).sub
      (ContDiffAt.sum (fun k _ => (hG i k j).smul (hE k)))
  have hden (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => d1 i j y • E j y+d2 i j y • E i y) x :=
    ((hd1 i j).smul (hE j)).add ((hd2 i j).smul (hE i))
  exact (((hR.pow 2).smul (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    (hQ i j).smul (hrow i j))))).sub
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => hden i j)))).add
    ((hR.pow 2).smul (ContDiffAt.sum (fun i _ => (hb i).smul (hE i))))

private lemma supported_two_operator_outputs {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U : R3 → V) (A B : R3 → V →L[ℝ] W) (K : Set R3) (hK : IsCompact K)
    (hU : ContDiff ℝ ∞ U) (h0 : ∀ x ∉ K,U x=0)
    (hA : ∀ x ∈ K,ContDiffAt ℝ ∞ A x) (hB : ∀ x ∈ K,ContDiffAt ℝ ∞ B x) :
    ContDiff ℝ ∞ (fun x => A x (U x)) ∧ ContDiff ℝ ∞ (fun x => B x (U x)) ∧
    HasCompactSupport (fun x => A x (U x)) ∧ HasCompactSupport (fun x => B x (U x)) := by
  exact ⟨ActualHigherSScalarCommutatorForm.contDiff_supported_operator_apply
      U A K hK.isClosed hU h0 hA,
    ActualHigherSScalarCommutatorForm.contDiff_supported_operator_apply U B K hK.isClosed hU h0 hB,
    ActualHigherSScalarCommutatorForm.compact_supported_operator_apply U A K hK h0,
    ActualHigherSScalarCommutatorForm.compact_supported_operator_apply U B K hK h0⟩

private lemma scalar_radius_smooth (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) :
    ContDiff ℝ ∞ (referenceRadius dr Ar p L) :=
  ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr

private lemma scalar_Q_smooth (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) := by
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have hcomp := (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp hqy
  simpa only [Function.comp_def] using hcomp

private lemma scalar_drift_smooth (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)) := by
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have hcomp := (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp hqy
  simpa only [Function.comp_def] using hcomp

private lemma scalar_frame_smooth (hg : IsAdmissibleMetric g) (q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceMetricGramFrame g L (q,y) i) := by
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have hcomp := (contDiff_referenceMetricGramFrame g hg L i).comp hqy
  simpa only [Function.comp_def] using hcomp

private lemma scalar_connection_smooth (hg : IsAdmissibleMetric g) (q : ℝ) (i k j : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j) :=
  ActualHigherSFormation.contDiff_referenceGramConnectionSlice g hg L q i j k

private lemma scalar_log_smooth (hg : IsAdmissibleMetric g) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y : R3 => referenceRadiusHorizontalLogDerivative g L q
      (referenceRadius dr Ar p L) y i) := by
  have hR : ContDiff ℝ ∞ (referenceRadius dr Ar p L) := scalar_radius_smooth L dr Ar p hdr hAr
  have hr : ∀ y : R3,referenceRadius dr Ar p L y ≠ 0 :=
    fun y => (referenceRadius_pos dr Ar p L y hdr hAr).ne'
  exact ActualHigherSIntegratedPairing.contDiff_logDerivative_slice
    (g := g) (L := L) (q := q) (R := referenceRadius dr Ar p L) hg hR hr i

private lemma scalar_density_derivative_smooth (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (i j k : Fin 3) :
    ContDiff ℝ ∞ (normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j k) :=
  contDiff_normalizedSecondCoefficientDerivative g L hg g2 hg2 dr Ar p hdr hAr q i j k

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceRadiusHorizontalLogDerivative normalizedSecondCoefficientDerivative referenceRadius

private lemma actual_linear_scalar_smooth (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) :
    ContDiff ℝ ∞ (referenceRadius dr Ar p L) ∧
    (∀ i j : Fin 3,ContDiff ℝ ∞ (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)) ∧
    (∀ i : Fin 3,ContDiff ℝ ∞ (fun y : R3 => normalizedSecondDriftFrameJoint g g2 L i (q,y))) ∧
    (∀ i : Fin 3,ContDiff ℝ ∞ (fun y : R3 => referenceMetricGramFrame g L (q,y) i)) ∧
    (∀ i k j : Fin 3,ContDiff ℝ ∞ (fun y : R3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j)) ∧
    (∀ i : Fin 3,ContDiff ℝ ∞ (fun y : R3 => referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) y i)) ∧
    (∀ i j k : Fin 3,ContDiff ℝ ∞ (normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j k)) := by
  exact ⟨scalar_radius_smooth L dr Ar p hdr hAr,
    scalar_Q_smooth g L hg g2 hg2 q,
    scalar_drift_smooth g L hg g2 hg2 q,
    scalar_frame_smooth g L hg q,
    scalar_connection_smooth g L hg q,
    scalar_log_smooth g L hg dr Ar p hdr hAr q,
    scalar_density_derivative_smooth g L hg g2 hg2 dr Ar p hdr hAr q⟩

attribute [local irreducible] canonicalHigh orderedReverseHigh linearZeroHigh linearAdjointZeroHigh

variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

private lemma linear_zero_forward_contDiffAt
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiffAt ℝ ∞ (Z1 g2 dr Ar p q) x := by
  obtain ⟨hR,hQ,hbSmooth,hX,hG,hf,hden⟩ := actual_linear_scalar_smooth
    g L hg g2 hg2 dr Ar p hdr hAr q
  let R := referenceRadius dr Ar p L
  let QF := fun i j y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let fF := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
  let bF := fun i y => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let XF := fun i y => referenceMetricGramFrame g L (q,y) i
  let GF := fun i k j y => referenceFrameConnectionCoefficient g L q y (XF i y) k j
  let EF : Fin 3 → R3 → Hi →L[ℝ] Half := fun i y => EH i ((Tq dr Ar p q) y)
  let DF : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Half := fun i j y => fderiv ℝ (EF j) y (XF i y)
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hE (i : Fin 3) : ContDiffAt ℝ ∞ (EF i) x := (he i).2.2.1.1
  have hD (i j : Fin 3) : ContDiffAt ℝ ∞ (DF i j) x :=
    ((hE j).fderiv_right (m := ∞) (by simp)).clm_apply (hX i).contDiffAt
  have hRows : ContDiffAt ℝ ∞ (forwardLinearRows R QF fF bF GF EF DF) x :=
    contDiffAt_forwardLinearRows R QF fF bF GF EF DF x hR.contDiffAt
      (fun i j => (hQ i j).contDiffAt) (fun i => (hf i).contDiffAt)
      (fun i => (hbSmooth i).contDiffAt) (fun i k j => (hG i k j).contDiffAt) hE hD
  have hFn : Z1 g2 dr Ar p q=forwardLinearRows R QF fF bF GF EF DF := by
    unfold linearZeroHigh forwardLinearRows
    rfl
  exact (congrArg (fun f => ContDiffAt ℝ ∞ f x) hFn).mpr hRows

private lemma linear_zero_reverse_contDiffAt
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiffAt ℝ ∞ (T1 g2 dr Ar p q) x := by
  obtain ⟨hR,hQ,hbSmooth,hX,hG,hf,hden⟩ := actual_linear_scalar_smooth
    g L hg g2 hg2 dr Ar p hdr hAr q
  let R := referenceRadius dr Ar p L
  let QF := fun i j y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let fF := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
  let bF := fun i y => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let XF := fun i y => referenceMetricGramFrame g L (q,y) i
  let GF := fun i k j y => referenceFrameConnectionCoefficient g L q y (XF i y) k j
  let EF : Fin 3 → R3 → Hi →L[ℝ] Half := fun i y => BH i ((Tq dr Ar p q) y)
  let DF : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Half := fun i j y => fderiv ℝ (EF i) y (XF j y)
  let d1 := fun i j y => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i y
  let d2 := fun i j y => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j y
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hE (i : Fin 3) : ContDiffAt ℝ ∞ (EF i) x := (he i).2.2.2.2.1.1
  have hD (i j : Fin 3) : ContDiffAt ℝ ∞ (DF i j) x :=
    ((hE i).fderiv_right (m := ∞) (by simp)).clm_apply (hX j).contDiffAt
  have hRows : ContDiffAt ℝ ∞ (reverseLinearRows R QF fF bF GF EF DF d1 d2) x :=
    contDiffAt_reverseLinearRows R QF fF bF GF EF DF d1 d2 x hR.contDiffAt
      (fun i j => (hQ i j).contDiffAt) (fun i => (hf i).contDiffAt)
      (fun i => (hbSmooth i).contDiffAt) (fun i k j => (hG i k j).contDiffAt) hE hD
      (fun i j => (hden i j i).contDiffAt) (fun i j => (hden i j j).contDiffAt)
  have hFn : T1 g2 dr Ar p q=reverseLinearRows R QF fF bF GF EF DF d1 d2 := by
    unfold linearAdjointZeroHigh reverseLinearRows
    rfl
  exact (congrArg (fun f => ContDiffAt ℝ ∞ f x) hFn).mpr hRows

/-- Original public paired regularity statement, collected from independent endpoints. -/
theorem linear_zero_high_contDiffAt
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiffAt ℝ ∞ (Z1 g2 dr Ar p q) x ∧ ContDiffAt ℝ ∞ (T1 g2 dr Ar p q) x := by
  exact ⟨linear_zero_forward_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs,
    linear_zero_reverse_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs⟩

theorem linear_zero_high_outputs_smooth_compact
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiff ℝ ∞ (fun x => Z1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    ContDiff ℝ ∞ (fun x => T1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    HasCompactSupport (fun x => Z1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    HasCompactSupport (fun x => T1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) := by
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F
  let ZA : R3 → Hi →L[ℝ] Half := Z1 g2 dr Ar p q
  let TA : R3 → Hi →L[ℝ] Half := T1 g2 dr Ar p q
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have h0 : ∀ x ∉ K,U x=0 := by
    intro x hx
    have hxF : x ∉ tsupport F.val := fun ht => hx (hsupp ht)
    exact ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x
      (image_eq_zero_of_notMem_tsupport hxF)
  have hC (x : R3) (hx : x ∈ K) : ContDiffAt ℝ ∞ ZA x ∧ ContDiffAt ℝ ∞ TA x :=
    linear_zero_high_contDiffAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (ball_subset_closedBall (hKball hx))
      (hKball hx) (hb x hx) (hs x hx)
  exact supported_two_operator_outputs U ZA TA K hK hU h0
    (fun x hx => (hC x hx).1) (fun x hx => (hC x hx).2)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZero
