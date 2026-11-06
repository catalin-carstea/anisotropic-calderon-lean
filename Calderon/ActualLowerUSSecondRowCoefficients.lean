import Calderon.ActualModelSErrorDecomposition
import Calderon.ActualMixedAngularPhysicalBounds
import Calderon.ActualHigherSCoordinateWeightBounds
import Calderon.ActualFiniteHarmonicModelBAngularPartUniform

/-!
GPT-6.1 Sol authoring support. The before-code expansion is
lower-u-s-nov03-v001/first-row-expansion.md. This module concerns only
the second-base lower U/S weak row, with full physical E coefficients.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows
  ActualMixedAngularPairedGains ActualHigherSLeadingBracketGain ActualHigherSCoordinateWeightBounds
  SmoothMetricFrame MovingFrameConnection ConformalDepth ReferenceWeightedApproximation
  ReferenceDensityBounds NormalizedPrincipalMetric ActualPhysicalMixedFirst
  FixedParameterProfilePullback

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section FiniteAlgebra
variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Exact finite linearity of a compatible commutator endpoint. -/
private lemma linear_combination_graph {ι : Type*} [Fintype ι]
    (I : U →L[ℝ] V) (EH : U →L[ℝ] V) (EL : V →L[ℝ] W)
    (GH : ι → U →L[ℝ] V) (GLo : ι → V →L[ℝ] W) (K : ι → V →L[ℝ] W)
    (c : ι → ℝ) (u : U)
    (h : ∀ i, K i (I u) = GLo i (EH u) - EL (GH i u)) :
    (∑ i, c i • K i) (I u) =
      (∑ i, c i • GLo i) (EH u) - EL ((∑ i, c i • GH i) u) := by
  simp only [sum_apply,smul_apply,map_sum,map_smul]
  simp_rw [h,smul_sub]
  simp only [Finset.sum_sub_distrib]

/-- A scalar-normalized compatible inclusion contributes zero to the bracket. -/
private lemma add_scalar_graph
    (I : U →L[ℝ] V) (J : V →L[ℝ] W) (EH : U →L[ℝ] V) (EL : V →L[ℝ] W)
    (DH : U →L[ℝ] V) (DL K : V →L[ℝ] W) (s : ℝ) (u : U)
    (hE : J (EH u) = EL (I u))
    (hK : K (I u) = DL (EH u) - EL (DH u)) :
    K (I u) = ((s • J) + DL) (EH u) - EL (((s • I) + DH) u) := by
  simp only [add_apply,smul_apply,map_add,map_smul]
  rw [← hE,hK]
  module

end FiniteAlgebra

/-- The operator-norm inequality needs only bounded scalar multiplication;
it does not assert an exact norm-scalar instance on the endpoint-map space. -/
theorem norm_smul_low_le (r : ℝ) (A : Half →L[ℝ] Neg) :
    ‖r • A‖ ≤ |r| * ‖A‖ := by
  simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le r A

/-- A concrete low-map finite sum estimate with all maps treated as typed
parameters. This keeps scalar-norm reasoning separate from endpoint data. -/
theorem norm_nonneg_smul_three_sum_le (r MW MB : ℝ) (hr : 0 ≤ r) (hMW : 0 ≤ MW)
    (c : Fin 3 → ℝ) (A : Fin 3 → Half →L[ℝ] Neg)
    (hc : ∀ i, |c i| ≤ MW) (hA : ∀ i, ‖A i‖ ≤ MB) :
    ‖r • (∑ i : Fin 3, c i • A i)‖ ≤ r*(3*MW*MB) := by
  have hn0 : ‖r • (∑ i : Fin 3, c i • A i)‖ ≤
      |r| * ‖∑ i : Fin 3, c i • A i‖ := norm_smul_low_le r (∑ i : Fin 3, c i • A i)
  have hs : |r| ≤ r := le_of_eq (abs_of_nonneg hr)
  have hn : ‖r • (∑ i : Fin 3, c i • A i)‖ ≤
      r * ‖∑ i : Fin 3, c i • A i‖ :=
    hn0.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg (∑ i : Fin 3, c i • A i)))
  calc
    _ ≤ r * ‖∑ i : Fin 3, c i • A i‖ := hn
    _ ≤ r * (∑ _i : Fin 3, MW*MB) := by
      apply mul_le_mul_of_nonneg_left _ hr
      apply (norm_sum_le Finset.univ (fun i : Fin 3 => c i • A i)).trans
      exact Finset.sum_le_sum (fun i _ =>
        (norm_smul_low_le (c i) (A i)).trans
          (mul_le_mul (hc i) (hA i) (norm_nonneg (A i)) hMW))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

/-- Degree/rotation index followed by a lowering index; no raising generators. -/
abbrev FirstAngularIndex := Generator ⊕ Fin 3

/-- Literal coefficients of the angular part of the lower U-adjoint first row.
The rotation coefficient is negative because generatorSharp is minus rotation. -/
def firstAngularCoefficient (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i : Fin 3) (x : R3) : FirstAngularIndex → ℝ
  | Sum.inl (Sum.inr _) => -nativeFirstDegreeCoefficient g g2 L q dr Ar p i x
  | Sum.inl (Sum.inl (b,d)) => -(1/2 : ℝ) * ∑ c : Fin 3,
      nativeFirstConnectionCoefficient g g2 L q dr Ar p i c x *
        referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) c) b d
  | Sum.inr b => -physicalMixedFirstCoefficient g L q
      (referenceNormalizedPrincipalDifference g g2 L q) b i x

def firstAngularHigh : FirstAngularIndex → Hi →L[ℝ] Half
  | Sum.inl V => generatorSharpHigh V
  | Sum.inr b => loweringHigh hF hO hD b

def firstAngularLow : FirstAngularIndex → Half →L[ℝ] Neg
  | Sum.inl V => generatorSharpLow V
  | Sum.inr b => loweringLow hF hO hD b

/-- Actual original scalar, degree, connection and lowering first coefficient,
at the high endpoint. The chosen scalar is the original native coefficient. -/
def lowerAdjointFirstHigh (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i : Fin 3) (x : R3) : Hi →L[ℝ] Half :=
  (-nativeFirstScalarCoefficient g g2 L q dr Ar p i x) • IH +
    ∑ v : FirstAngularIndex,
      firstAngularCoefficient g L g2 q dr Ar p i x v • firstAngularHigh hF hO hD v

def lowerAdjointFirstLow (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i : Fin 3) (x : R3) : Half →L[ℝ] Neg :=
  (-nativeFirstScalarCoefficient g g2 L q dr Ar p i x) • JL +
    ∑ v : FirstAngularIndex,
      firstAngularCoefficient g L g2 q dr Ar p i x v • firstAngularLow hF hO hD v

/-- Concrete gain from retained endpoint rooms on exactly data.δ0/data.germs. -/
def firstAngularGain (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) : FirstAngularIndex → Half →L[ℝ] Neg
  | Sum.inl V => gen.low V j t
  | Sum.inr b => mixed.Bl b j t

def firstGainCombination (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3) : Half →L[ℝ] Neg :=
  ∑ v : FirstAngularIndex, firstAngularCoefficient g L g2 q dr Ar p i x v •
    firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j ((Tq dr Ar p q) x) v

/-- Literal second-base weak row [D_i,P_j], with the original contracted
full physical S first coefficient. It is a gained low endpoint, not a residual. -/
def lowerUSSecondCoefficient (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3) : Half →L[ℝ] Neg :=
  (referenceRadius dr Ar p L x)^2 • (∑ b : Fin 3,
    firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
      firstGainCombination g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen g2 q dr Ar p i b x)

local notation "FG" => firstGainCombination
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "TC" => lowerUSSecondCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Endpoint graph for each genuine retained generator/lowering gain. -/
theorem firstAngularGain_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (v : FirstAngularIndex) (u : Hi) :
    firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t v (IH u) =
      firstAngularLow hF hO hD v (EH j t u) - EL j t (firstAngularHigh hF hO hD v u) := by
  cases v with
  | inl V =>
    have hu := congrArg (fun A : Hi →L[ℝ] Neg => A u) (gen.upper V j t htG)
    exact hu.trans (gen.highGraph V j t htG u)
  | inr b =>
    have hh := mixed.graphs b j t htM
    have hu := congrArg (fun A : Hi →L[ℝ] Neg => A u) hh.2.2.1
    exact hu.trans (hh.1 u)

/-- Exact graph before contraction into the original S coordinate coefficient.
The scalar compatibility is an explicit intermediate identity, not a norm premise. -/
theorem firstGainCombination_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hE : ∀ u : Hi, JL (EH j ((Tq dr Ar p q) x) u) =
      EL j ((Tq dr Ar p q) x) (IH u)) (u : Hi) :
    FG mixed δ gen g2 q dr Ar p i j x (IH u) =
      lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x (EH j ((Tq dr Ar p q) x) u) -
      EL j ((Tq dr Ar p q) x) (lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p i x u) := by
  have h := linear_combination_graph IH (EH j ((Tq dr Ar p q) x)) (EL j ((Tq dr Ar p q) x))
    (firstAngularHigh hF hO hD) (firstAngularLow hF hO hD)
    (firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j ((Tq dr Ar p q) x))
    (firstAngularCoefficient g L g2 q dr Ar p i x) u
    (fun v => firstAngularGain_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j ((Tq dr Ar p q) x) htG htM v u)
  exact add_scalar_graph IH JL (EH j ((Tq dr Ar p q) x)) (EL j ((Tq dr Ar p q) x))
    _ _ _ (-nativeFirstScalarCoefficient g g2 L q dr Ar p i x) u (hE u) h

/-- Exact [D_i,P_j] graph on the original high domain. P is the actual
full physical S first coordinate coefficient, with both Q orders retained. -/
theorem lowerUSSecondCoefficient_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hE : ∀ b : Fin 3, ∀ u : Hi, JL (EH b ((Tq dr Ar p q) x) u) =
      EL b ((Tq dr Ar p q) x) (IH u)) (u : Hi) :
    TC mixed δ gen g2 q dr Ar p i j x (IH u) =
      lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x
        (((referenceRadius dr Ar p L x)^2 •
          (∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
            EH b ((Tq dr Ar p q) x))) u) -
      ((referenceRadius dr Ar p L x)^2 •
        (∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
          EL b ((Tq dr Ar p q) x)))
        (lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p i x u) := by
  simp only [lowerUSSecondCoefficient,smul_apply,sum_apply,map_smul,map_sum]
  simp_rw [firstGainCombination_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data mixed δ gen g2 q dr Ar p i _ x htG htM (hE _) u]
  simp only [smul_sub,Finset.sum_sub_distrib]

/-- The ordinary E compatibility is produced from the original retained germs
and physical endpoint room; the final graph has no analytic callback. -/
theorem lowerUSSecondCoefficient_graph_of_room (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (htData : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (u : Hi) :
    TC mixed δ gen g2 q dr Ar p i j x (IH u) =
      lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p i x
        (((referenceRadius dr Ar p L x)^2 •
          (∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
            EH b ((Tq dr Ar p q) x))) u) -
      ((referenceRadius dr Ar p L x)^2 •
        (∑ b : Fin 3, firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x) •
          EL b ((Tq dr Ar p q) x)))
        (lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p i x u) := by
  have ht0 : (Tq dr Ar p q) x ∈ ParamRoom data.δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 htData.1,htData.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset ((Tq dr Ar p q) x).1 htData.1
  have hE (b : Fin 3) (v : Hi) : JL (EH b ((Tq dr Ar p q) x) v) =
      EL b ((Tq dr Ar p q) x) (IH v) := by
    have hp := (data.germs.piGerm b ((Tq dr Ar p q) x) ht0).self_of_nhds
    exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg b ((Tq dr Ar p q) x) hSeg
      (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        data.δ0 data.germs b ((Tq dr Ar p q) x)) hp.1 hp.2.1 v
  exact lowerUSSecondCoefficient_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data mixed δ gen g2 q dr Ar p i j x htG htM hE u

/-- Exact coefficient mass: replacing forward raising by adjoint lowering
costs no new angular coefficient budget. -/
theorem firstAngularCoefficient_mass_le (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i : Fin 3) (x : R3) :
    (∑ v : FirstAngularIndex, |firstAngularCoefficient g L g2 q dr Ar p i x v|) ≤
      nativeBAngularPartMass g g2 L q dr Ar p i x := by
  let k : Fin 3 → ℝ := fun c => nativeFirstConnectionCoefficient g g2 L q dr Ar p i c x
  let Γ : Fin 3 → Fin 3 → Fin 3 → ℝ := fun c b d =>
    referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) c) b d
  have hr (b d : Fin 3) : |-(1/2 : ℝ) * ∑ c : Fin 3, k c * Γ c b d| ≤
      (1/2 : ℝ) * ∑ c : Fin 3, |k c| * |Γ c b d| := by
    rw [abs_mul,abs_neg,abs_of_pos (by norm_num : 0 < (1/2 : ℝ))]
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_mul])) (by norm_num)
  have hrs : (∑ b : Fin 3, ∑ d : Fin 3,
      |-(1/2 : ℝ) * ∑ c : Fin 3, k c * Γ c b d|) ≤
      ∑ c : Fin 3, |k c| * ((1/2 : ℝ) * ∑ b : Fin 3, ∑ d : Fin 3, |Γ c b d|) := by
    calc
      _ ≤ ∑ b : Fin 3, ∑ d : Fin 3,
          (1/2 : ℝ) * ∑ c : Fin 3, |k c| * |Γ c b d| :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun d _ => hr b d))
      _ = _ := by
        simp only [Fin.sum_univ_three]
        ring
  simpa only [FirstAngularIndex,Generator,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fintype.sum_unique,firstAngularCoefficient,abs_neg,nativeBAngularPartMass,
    nativeReferenceConnectionCoefficientMass,k,Γ,add_comm,add_left_comm,add_assoc] using
      add_le_add_right (add_le_add_left hrs
        |nativeFirstDegreeCoefficient g g2 L q dr Ar p i x|)
        (∑ b : Fin 3, |physicalMixedFirstCoefficient g L q
          (referenceNormalizedPrincipalDifference g g2 L q) b i x|)

/-- A common low endpoint cap is derived internally from the retained joint
caps of the two actual rooms, on their common parameter region. -/
theorem exists_firstAngularGain_joint_cap (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ ParamRoom δ, t ∈ ParamRoom mixed.δ →
      ∀ j : Fin 3, ∀ v : FirstAngularIndex,
      ‖firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t v‖ ≤ M := by
  obtain ⟨MG,hMG,hG⟩ := gen.finiteCaps 0
  obtain ⟨MM,hMM,hM⟩ := mixed.joint_caps 0
  refine ⟨1+MG+MM,by linarith,?_⟩
  intro t htG htM j v
  cases v with
  | inl V =>
    have hh : ‖gen.low V j t‖ ≤ MG := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hG V j 0 (le_refl 0) t htG).2.2
    exact hh.trans (by linarith)
  | inr b =>
    have hh : ‖mixed.Bl b j t‖ ≤ MM := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hM b j 0 (le_refl 0) t htM).2.2
    exact hh.trans (by linarith)

theorem norm_firstGainCombination_le (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3)
    (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ v : FirstAngularIndex,
      ‖firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M) :
    ‖FG mixed δ gen g2 q dr Ar p i j x‖ ≤
      M * nativeBAngularPartMass g g2 L q dr Ar p i x := by
  calc
    _ ≤ ∑ v : FirstAngularIndex,
        |firstAngularCoefficient g L g2 q dr Ar p i x v| * M := by
      unfold firstGainCombination
      apply (norm_sum_le Finset.univ (fun v : FirstAngularIndex =>
        firstAngularCoefficient g L g2 q dr Ar p i x v •
          firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
            mixed δ gen j ((Tq dr Ar p q) x) v)).trans
      exact Finset.sum_le_sum (fun v _ =>
        (norm_smul_low_le (firstAngularCoefficient g L g2 q dr Ar p i x v)
          (firstAngularGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
            mixed δ gen j ((Tq dr Ar p q) x) v)).trans
          (mul_le_mul_of_nonneg_left (hcap v)
            (abs_nonneg (firstAngularCoefficient g L g2 q dr Ar p i x v))))
    _ = M * (∑ v : FirstAngularIndex, |firstAngularCoefficient g L g2 q dr Ar p i x v|) := by
      rw [← Finset.sum_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (firstAngularCoefficient_mass_le g L g2 q dr Ar p i x) hM


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
