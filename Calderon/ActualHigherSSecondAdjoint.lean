import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualHigherSPhysicalIntegratedConsumer
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSecondAdjoint
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ActualHorizontalNormBridge
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Original density-weighted divergence correction, including the derivative of a. -/
def densityDerivativeCoefficient (g : MatrixField) (L q : ℝ) (i : Fin 3)
    (a : R3 → ℝ) (x : R3) : ℝ :=
  a x * referenceWeightedFrameDivergence g L q i x +
    referenceDensityFamily g L (q,x) * fderiv ℝ a x (referenceMetricGramFrame g L (q,x) i)

lemma contDiff_densityDerivativeCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) (a : R3 → ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (densityDerivativeCoefficient g L q i a) := by
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hdiv := ActualHigherSPhysicalPairing.contDiff_referenceWeightedFrameDivergence g hg L q i
  have hX := contDiff_referenceMetricGramFrame_slice g hg L q i
  exact (ha.mul hdiv).add (hmu.mul ((contDiff_infty_iff_fderiv.1 ha).2.clm_apply hX))

/-- The exact density normalization is available everywhere for the original admissible metric. -/
lemma density_mul_inv_half (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (x : R3) (v : Half) :
    referenceDensityFamily g L (q,x) • ((referenceDensityFamily g L (q,x))⁻¹ • v) = v := by
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (referenceDensityFamily_pos g hg L (q,x))),one_smul]


attribute [local irreducible] referenceRadius referenceDensityPrincipalFrameCoefficient

/-- The unchanged coefficient r² Q_ij of the Second block. -/
def secondCoefficient (g g2 : MatrixField) (L q δr Ar : ℝ) (p : ℕ)
    (i j : Fin 3) (x : R3) : ℝ :=
  (referenceRadius δr Ar p L x)^2 * referenceDensityPrincipalFrameCoefficient g g2 L q x i j

lemma contDiff_secondCoefficient (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L q δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (i j : Fin 3) : ContDiff ℝ ∞ (secondCoefficient g g2 L q δr Ar p i j) :=
by
  have hr : ContDiff ℝ ∞ (referenceRadius δr Ar p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hQ : ContDiff ℝ ∞ (fun x : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q x i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (contDiff_const.prodMk contDiff_id)
  exact (hr.pow 2).mul hQ

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "eH" => ActualGeneratorEPairedGainedEndpoints.reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "UB" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "UD" => ActualHigherSFormation.higherSReferenceInput hO hD g L hg
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- Literal density-multiplied reverse of the original derivative/Second S block.
Both coefficient derivatives, both degree corrections, Γ and b are retained. -/
def revSecondDensityHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  let R := referenceRadius δr Ar p L
  let μ := referenceDensityFamily g L (q,x)
  let aij := secondCoefficient g g2 L q δr Ar p
  let fi := referenceRadiusHorizontalLogDerivative g L q R x
  let Γ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j
  let er := fun j : Fin 3 => eH j ((Tq δr Ar p q) x) (Uin F0 x)
  let row1 : Fin 3 → Fin 3 → Half := fun i j =>
    (-(μ * aij i j x)) • eH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F0 i x) +
      (2 * (μ * aij i j x * fi i)) • eH j ((Tq δr Ar p q) x) (UB F0 x) -
      densityDerivativeCoefficient g L q i (aij i j) x • er j
  let row2 : Fin 3 → Fin 3 → Half := fun i j =>
    (-(μ * aij i j x)) • referenceHighWeightedHorizontalAction g L q R
        (VR hreg δ0 W δr Ar p q F0 i) x j +
      (2 * (μ * aij i j x * fi j)) •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W δr Ar p q F0 i x) : Half) -
      densityDerivativeCoefficient g L q j (aij i j) x • IH (VR hreg δ0 W δr Ar p q F0 i x)
  (∑ i : Fin 3, ∑ j : Fin 3,
    (row1 i j + row2 i j + (μ * aij i j x * fi i) • er j -
      ∑ k : Fin 3, (μ * aij i j x * Γ i j k) • er k)) +
    ∑ i : Fin 3, (μ * ((R x)^2 * normalizedSecondDriftFrameJoint g g2 L i (q,x))) • er i

/-- The actual Half adjoint normalized in the original positive physical density. -/
def revSecondHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  (referenceDensityFamily g L (q,x))⁻¹ •
    revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x
local notation "RD" => revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma density_mul_revSecondHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    referenceDensityFamily g L (q,x) • RH hreg δ0 W g2 δr Ar p hδr hAr q F0 x =
      RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x :=
  density_mul_inv_half g hg L q x _

lemma revSecondDensityHalf_eq_zero_off_support (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    RD hreg δ0 W g2 δr Ar p hδr hAr q F0 z = 0 := by
  have hu0 := ActualReverseEHigherLift.revInput_eq_zero hO hD F0 z hz
  have hb0 := ActualReverseEHigherLift.revDegreeInput_eq_zero hO hD F0 z hz
  have hd0 (i : Fin 3) := ActualHigherSFormation.higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0 i z hz
  have hr0 (i : Fin 3) := ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 i z hz
  have hDW0 (i j : Fin 3) : referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (VR hreg δ0 W δr Ar p q F0 i) z j = 0 := by
    apply ActualHigherSFormation.referenceHighWeightedHorizontalAction_eq_zero_of_eventually
    filter_upwards [ActualHigherSFormation.notMem_tsupport_eventually hO hD F0 z hz] with x hx
    exact ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w
      hData hg hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 i x hx
  simp only [revSecondDensityHalf,hu0,hb0,hd0,hr0,hDW0,map_zero,smul_zero,
    add_zero,sub_zero,Finset.sum_const_zero]

lemma revSecondHalf_eq_zero_off_support (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    RH hreg δ0 W g2 δr Ar p hδr hAr q F0 z = 0 := by
  rw [revSecondHalf,revSecondDensityHalf_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q F0 z hz,smul_zero]

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  ActualGeneratorEPairedGainedEndpoints.reverseEHigh
  ActualReverseEHigherLift.reverseEHigherLift


/-- Global smooth formation of the density-multiplied derivative adjoint on one
retained W/room, with the original membership-only premise. -/
theorem contDiff_revSecondDensityHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (RD hreg δ0 W g2 δr Ar p hδr hAr q F0) := by
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have ha (i j : Fin 3) := contDiff_secondCoefficient g g2 hg hg2 L q δr Ar p hδr hAr i j
  have hf (i : Fin 3) : ContDiff ℝ ∞ (fun x =>
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg (referenceRadius δr Ar p L) (q,x) i
        hR.contDiffAt (ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr))).comp x
        (contDiffAt_const.prodMk contDiffAt_id))
  have hGamma (i j k : Fin 3) := ActualHigherSFormation.contDiff_referenceGramConnectionSlice g hg L q i j k
  have hb (i : Fin 3) : ContDiff ℝ ∞ (fun x => normalizedSecondDriftFrameJoint g g2 L i (q,x)) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (contDiff_const.prodMk contDiff_id)
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUB := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
  have hU0 := ActualReverseEHigherLift.revInput_eq_zero hO hD F0
  have hUB0 := ActualReverseEHigherLift.revDegreeInput_eq_zero hO hD F0
  have hUD (i : Fin 3) : ContDiff ℝ ∞ (UD δr Ar p hδr hAr q F0 i) :=
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (coreReferenceInput hO hD g hg L q δr Ar p i hδr hAr F0)
  have hUD0 (i : Fin 3) := ActualHigherSFormation.higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0 i
  have he (j : Fin 3) : ContDiff ℝ ∞ (fun x => eH j ((Tq δr Ar p q) x) (Uin F0 x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
      (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (Uin F0) hU hU0
  have heB (j : Fin 3) : ContDiff ℝ ∞ (fun x => eH j ((Tq δr Ar p q) x) (UB F0 x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
      (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (UB F0) hUB hUB0
  have heD (j i : Fin 3) : ContDiff ℝ ∞ (fun x => eH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F0 i x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
      (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (UD δr Ar p hδr hAr q F0 i) (hUD i) (hUD0 i)
  have hvr (i : Fin 3) := ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hT i
  have hIv (i : Fin 3) : ContDiff ℝ ∞ (fun x => IH (VR hreg δ0 W δr Ar p q F0 i x)) :=
    (IH).contDiff.comp (hvr i)
  have hBv (i : Fin 3) : ContDiff ℝ ∞ (fun x =>
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W δr Ar p q F0 i x) : Half)) :=
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)).contDiff.comp (hvr i)
  have hDv (j i : Fin 3) : ContDiff ℝ ∞ (fun x => referenceHighWeightedHorizontalAction g L q
      (referenceRadius δr Ar p L) (VR hreg δ0 W δr Ar p q F0 i) x j) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      contDiffAt_referenceHighWeightedHorizontalAction g hg L q (referenceRadius δr Ar p L)
        (VR hreg δ0 W δr Ar p q F0 i) x j hR.contDiffAt
        (ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)) (hvr i).contDiffAt)
  have hdc (i j k : Fin 3) := contDiff_densityDerivativeCoefficient g hg L q k
    (secondCoefficient g g2 L q δr Ar p i j) (ha i j)
  have hwa (i j : Fin 3) := hmu.mul (ha i j)
  have htw (i j k : Fin 3) :=
    (show ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ)) from contDiff_const).mul ((hwa i j).mul (hf k))
  have hrow1 (i j : Fin 3) :=
    (((hwa i j).neg.smul (heD j i)).add ((htw i j i).smul (heB j))).sub ((hdc i j i).smul (he j))
  have hrow2 (i j : Fin 3) :=
    (((hwa i j).neg.smul (hDv j i)).add ((htw i j j).smul (hBv i))).sub ((hdc i j j).smul (hIv i))
  have hrow (i j : Fin 3) := (hrow1 i j).add (hrow2 i j)
  have hrowAll (i j : Fin 3) := ((hrow i j).add
    (((hmu.mul (ha i j)).mul (hf i)).smul (he j))).sub
      (ContDiff.sum (s := Finset.univ) (fun (k : Fin 3) _ => (((hmu.mul (ha i j)).mul (hGamma i j k)).smul (he k))))
  exact (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => hrowAll i j))).add
    (ContDiff.sum (fun i _ => (hmu.mul ((hR.pow 2).mul (hb i))).smul (he i)))

/-- The normalized derivative adjoint is also globally smooth in the original density. -/
theorem contDiff_revSecondHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (RH hreg δ0 W g2 δr Ar p hδr hAr q F0) :=
  ((contDiff_referenceDensityFamily_inv g hg L).comp
    (show ContDiff ℝ ∞ (fun x : R3 => (q,x)) from contDiff_const.prodMk contDiff_id)).smul
    (contDiff_revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hT)

/-- Exact high input for the physical weighted derivative of a finite core. -/
lemma referenceInput_inclusion (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (F0 : smoothCompactFiniteSphereCore hO hD)
    (i : Fin 3) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (coreReferenceInput hO hD g hg L q δr Ar p i hδr hAr F0) x) =
      referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
        (ActualHigherSFormation.higherSInput hO hD F0) x i :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreReferenceInput hO hD g hg L q δr Ar p i hδr hAr F0) x).trans
    (referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δr Ar p hδr hAr F0 x i).symm

attribute [local irreducible] referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceRadiusHorizontalLogDerivative sphereSobolevDualPairing


private lemma pp_sub_right_local (a : Half) (b c : Neg) : PP a (b-c) = PP a b-PP a c := by
  unfold sphereSobolevDualPairing
  exact inner_sub_right a b c

private lemma integral_three_of_eq (F X Y Z : R3 → ℝ)
    (hX : Integrable X) (hY : Integrable Y) (hZ : Integrable Z)
    (h : ∀ x, F x = -X x + 2 * Y x - Z x) :
    (∫ x, F x) = -(∫ x, X x) + 2 * (∫ x, Y x) - ∫ x, Z x := by
  have hA : Integrable (fun x => -X x + 2 * Y x) := hX.neg.add (hY.const_mul 2)
  calc
    (∫ x, F x) = ∫ x, -X x + 2 * Y x - Z x :=
      integral_congr_ae (Filter.Eventually.of_forall h)
    _ = (∫ x, -X x + 2 * Y x) - ∫ x, Z x :=
      integral_sub (f := fun x => -X x + 2 * Y x) (g := Z) hA hZ
    _ = ((∫ x, -X x) + ∫ x, 2 * Y x) - ∫ x, Z x :=
      congrArg (fun z : ℝ => z - ∫ x, Z x)
        (integral_add (f := fun x => -X x) (g := fun x => 2 * Y x) hX.neg (hY.const_mul 2))
    _ = _ := by rw [integral_neg,integral_const_mul]

/-- Internal Half output for the existing scalar Green identity. This is only
an exact repackaging used in the Second Sdag construction. -/
private def densityHorizontalReverse (g : MatrixField) (L q : ℝ) (R a : R3 → ℝ)
    (u : R3 → Hi) (i : Fin 3) (x : R3) : Half :=
  (-(referenceDensityFamily g L (q,x) * a x)) •
      referenceHighWeightedHorizontalAction g L q R u x i +
    (2 * (referenceDensityFamily g L (q,x) * a x *
      referenceRadiusHorizontalLogDerivative g L q R x i)) •
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x) : Half) -
    densityDerivativeCoefficient g L q i a x • IH (u x)

attribute [local irreducible] densityHorizontalReverse

private lemma scalar_middle_comm (m f a b : ℝ) : m*f*a*b = m*a*f*b := by ring

private lemma scalar_green_density_adjoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (R a : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (hr : ∀ x, R x ≠ 0)
    (u : R3 → Hi) (v : R3 → Half) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    (∫ x, referenceDensityFamily g L (q,x) * a x *
      PP (IH (u x)) (referenceLowerWeightedHorizontalAction g L q R v x i)) =
      ∫ x, PP (v x) (JL (densityHorizontalReverse g L q R a u i x)) := by
  let μ : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let D : R3 → Half := fun x => referenceHighWeightedHorizontalAction g L q R u x i
  let B : R3 → Half := fun x => (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x) : Half)
  let f : R3 → ℝ := fun x => referenceRadiusHorizontalLogDerivative g L q R x i
  let dc := densityDerivativeCoefficient g L q i a
  have hmu : ContDiff ℝ ∞ μ :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ f := contDiff_iff_contDiffAt.2 (fun x =>
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,x) i hR.contDiffAt (hr x)).comp x
      (contDiffAt_const.prodMk contDiffAt_id))
  have hD : ContDiff ℝ ∞ D := contDiff_iff_contDiffAt.2 (fun x =>
    contDiffAt_referenceHighWeightedHorizontalAction g hg L q R u x i hR.contDiffAt (hr x) hu.contDiffAt)
  have hB : ContDiff ℝ ∞ B := (sphereSobolevShiftedDegreeL (3/2 : ℝ)).contDiff.comp hu
  have hIu : ContDiff ℝ ∞ (fun x => IH (u x)) := (IH).contDiff.comp hu
  have hdc := contDiff_densityDerivativeCoefficient g hg L q i a ha
  have iX0 := ActualHigherSPhysicalIntegratedConsumer.integrable_mul_pp_right (fun x => μ x * a x) D v
    ((hmu.mul ha).continuous) hD.continuous hv.continuous hvc
  have iX : Integrable (fun x => μ x * a x * PP (v x) (JL (D x))) :=
    iX0.congr (Filter.Eventually.of_forall (fun x =>
      congrArg (fun z : ℝ => μ x * a x * z) (halfPairing_inclusion_symm (D x) (v x))))
  have iY0 := ActualHigherSPhysicalIntegratedConsumer.integrable_mul_pp_right (fun x => μ x * a x * f x) B v
    (((hmu.mul ha).mul hf).continuous) hB.continuous hv.continuous hvc
  have iY : Integrable (fun x => μ x * a x * f x * PP (v x) (JL (B x))) :=
    iY0.congr (Filter.Eventually.of_forall (fun x =>
      congrArg (fun z : ℝ => μ x * a x * f x * z) (halfPairing_inclusion_symm (B x) (v x))))
  have iZ : Integrable (fun x => dc x * PP (IH (u x)) (JL (v x))) :=
    ActualHigherSPhysicalIntegratedConsumer.integrable_mul_pp_right dc (fun x => IH (u x)) v
      hdc.continuous hIu.continuous hv.continuous hvc
  have hpt (x : R3) : PP (v x) (JL (densityHorizontalReverse g L q R a u i x)) =
      -(μ x * a x * PP (v x) (JL (D x))) +
        2 * (μ x * a x * f x * PP (v x) (JL (B x))) -
        dc x * PP (IH (u x)) (JL (v x)) := by
    simp only [densityHorizontalReverse,map_sub,map_add,map_smul,pp_sub_right_local,
      halfPairing_add_right,halfPairing_smul_right]
    rw [halfPairing_inclusion_symm (v x) (IH (u x))]
    dsimp only [μ,D,B,f,dc]
    ring
  have he := integral_three_of_eq _ _ _ _ iX iY iZ hpt
  have hG := ActualHigherSPhysicalIntegratedConsumer.scalar_weighted_green_combined g L q R hg hR hr
    u v a hu hv hvc ha i
  have hm : (fun x : R3 => μ x * f x * a x * PP (v x) (JL (B x))) =
      (fun x : R3 => μ x * a x * f x * PP (v x) (JL (B x))) := by
    funext x
    exact scalar_middle_comm _ _ _ _
  change (∫ x, μ x * a x * PP (IH (u x)) (referenceLowerWeightedHorizontalAction g L q R v x i)) =
    -(∫ x, μ x * a x * PP (v x) (JL (D x))) +
      2 * (∫ x, μ x * f x * a x * PP (v x) (JL (B x))) -
      ∫ x, dc x * PP (IH (u x)) (JL (v x)) at hG
  have hmi := congrArg (fun F : R3 → ℝ => ∫ x, F x) hm
  have hright := congrArg (fun z : ℝ =>
    -(∫ x, μ x * a x * PP (v x) (JL (D x))) + 2*z -
      ∫ x, dc x * PP (IH (u x)) (JL (v x))) hmi
  exact hG.trans (hright.trans he.symm)

/-- Internal exact transpose of a linear three-term output under the genuine E/e pivot. -/
private lemma transpose_E_three (E e : Hi →L[ℝ] Half)
    (hp : ∀ u v, PP (E u) (JL (IH v)) = PP (IH u) (JL (e v)))
    (u d b f : Hi) (s t c : ℝ) :
    PP (E u) (JL (s • IH d + t • IH b - c • IH f)) =
      PP (IH u) (JL (s • e d + t • e b - c • e f)) := by
  simp only [map_sub,map_add,map_smul,pp_sub_right_local,halfPairing_add_right,halfPairing_smul_right,hp]


local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

private def reverseFirstDerivativeRow (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr)
    (hAr : 0 < Ar) (q : ℝ) (c0 : R3 → ℝ) (i j : Fin 3)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  (-(referenceDensityFamily g L (q,x) * c0 x)) •
      eH j ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q F0 i x) +
    (2 * (referenceDensityFamily g L (q,x) * c0 x *
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)) •
      eH j ((Tq δr Ar p q) x) (UB F0 x) -
    densityDerivativeCoefficient g L q i c0 x • eH j ((Tq δr Ar p q) x) (Uin F0 x)
local notation "R1" => reverseFirstDerivativeRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- First derivative row of the exact Second adjoint: the original D_i E_j term.
The arbitrary smooth scalar c0 will be r²Q_ij; its derivative and density divergence stay literal. -/
theorem integrated_first_derivative_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (c0 : R3 → ℝ) (ha : ContDiff ℝ ∞ c0) (i j : Fin 3)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (∫ x, referenceDensityFamily g L (q,x) * c0 x * PP (IH (Uin F0 x))
      (JL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
        (VF δr Ar p q hreg δ0 W G0 j) x i))) =
      ∫ x, PP (IH (Uin G0 x)) (JL (R1 δr Ar p hδr hAr q c0 i j F0 x)) := by
  let R := referenceRadius δr Ar p L
  let U := Uin F0
  let V := VF δr Ar p q hreg δ0 W G0 j
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr (x : R3) : R x ≠ 0 := ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hV : ContDiff ℝ ∞ V := ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG j
  have hV0 := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W G0 j
  have hv : ContDiff ℝ ∞ (fun x => IH (V x)) := (IH).contDiff.comp hV
  have hvc : HasCompactSupport (fun x => IH (V x)) :=
    ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD G0 _
      (fun x hx => (congrArg (fun v : Hi => IH v) (show V x = 0 from hV0 x hx)).trans (map_zero IH))
  have hG := scalar_green_density_adjoint g hg L q R c0 hR hr U (fun x => IH (V x)) hU hv hvc ha i
  have hL :
      (∫ x, referenceDensityFamily g L (q,x) * c0 x * PP (IH (U x))
        (JL (referenceHighWeightedHorizontalAction g L q R V x i))) =
      ∫ x, referenceDensityFamily g L (q,x) * c0 x * PP (IH (U x))
        (referenceLowerWeightedHorizontalAction g L q R (fun z => IH (V z)) x i) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => congrArg
      (fun z : Neg => referenceDensityFamily g L (q,x) * c0 x * PP (IH (U x)) z)
      (ActualHigherSFormation.referenceWeightedHorizontalAction_inclusion g L q R V x i
        ((hV.differentiable (by simp)) x)))
  have hpt (x : R3) : PP (IH (V x)) (JL (densityHorizontalReverse g L q R c0 U i x)) =
      PP (IH (Uin G0 x)) (JL (R1 δr Ar p hδr hAr q c0 i j F0 x)) := by
    by_cases hx : x ∈ TS G0
    swap
    · have hu0 := ActualReverseEHigherLift.revInput_eq_zero hO hD G0 x hx
      simp only [show V x = 0 from hV0 x hx,hu0,map_zero,halfPairing_zero_left]
    let s : ℝ := -(referenceDensityFamily g L (q,x) * c0 x)
    let t : ℝ := 2 * (referenceDensityFamily g L (q,x) * c0 x *
      referenceRadiusHorizontalLogDerivative g L q R x i)
    let c : ℝ := densityDerivativeCoefficient g L q i c0 x
    have hd := referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F0 i x
    have hb := inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x
    have hden : densityHorizontalReverse g L q R c0 U i x =
        s • IH (UD δr Ar p hδr hAr q F0 i x) + t • IH (UB F0 x) - c • IH (U x) := by
      unfold densityHorizontalReverse
      exact congrArg₂ (fun d b : Half => s • d + t • b - c • IH (U x)) hd.symm hb.symm
    have hval : IH (V x) = EH j ((Tq δr Ar p q) x) (Uin G0 x) :=
      ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG j x
    have hp := transpose_E_three (EH j ((Tq δr Ar p q) x)) (eH j ((Tq δr Ar p q) x))
      (fun u v => Cm.pivot j _ (hTG x hx) u v) (Uin G0 x)
      (UD δr Ar p hδr hAr q F0 i x) (UB F0 x) (U x) s t c
    exact (congrArg₂ (fun v d : Half => PP v (JL d)) hval hden).trans hp
  exact hL.trans (hG.trans (integral_congr_ae (Filter.Eventually.of_forall hpt)))


private lemma pp_zero_right_local (u : Half) : PP u 0 = 0 := by
  unfold sphereSobolevDualPairing
  exact inner_zero_right u

/-- Second derivative row of the exact Second adjoint: the original E_i D_j term.
The weighted derivative acts on the existing genuine reverse high lift, including
both the original coefficient derivative and the physical degree correction. -/
theorem integrated_second_derivative_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (c0 : R3 → ℝ) (hc0 : ContDiff ℝ ∞ c0) (i j : Fin 3)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (∫ x, referenceDensityFamily g L (q,x) * c0 x * PP (IH (Uin F0 x))
      (JL (EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x)))) =
      ∫ x, PP (IH (Uin G0 x))
        (JL (densityHorizontalReverse g L q (referenceRadius δr Ar p L) c0
          (VR hreg δ0 W δr Ar p q F0 i) j x)) := by
  let R := referenceRadius δr Ar p L
  let U := Uin G0
  let V := VR hreg δ0 W δr Ar p q F0 i
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr (x : R3) : R x ≠ 0 := ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) G0
  have hV : ContDiff ℝ ∞ V := ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hTF i
  have hv : ContDiff ℝ ∞ (fun x => IH (U x)) := (IH).contDiff.comp hU
  have hU0 := ActualReverseEHigherLift.revInput_eq_zero hO hD G0
  have hvc : HasCompactSupport (fun x => IH (U x)) :=
    ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD G0 _
      (fun x hx => (congrArg (fun v : Hi => IH v) (show U x = 0 from hU0 x hx)).trans (map_zero IH))
  have hG := scalar_green_density_adjoint g hg L q R c0 hR hr V (fun x => IH (U x)) hV hv hvc hc0 j
  have hpt (x : R3) : PP (IH (Uin F0 x))
      (JL (EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x))) =
      PP (IH (V x)) (referenceLowerWeightedHorizontalAction g L q R (fun z => IH (U z)) x j) := by
    have hEP : PP (IH (Uin F0 x))
        (JL (EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x))) =
        PP (IH (UD δr Ar p hδr hAr q G0 j x)) (JL (eH i ((Tq δr Ar p q) x) (Uin F0 x))) := by
      by_cases hx : x ∈ TS G0
      · exact (halfPairing_inclusion_symm _ _).trans
          (Cm.pivot i _ (hTG x hx) (UD δr Ar p hδr hAr q G0 j x) (Uin F0 x))
      · have hd0 := ActualHigherSFormation.higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
          hData hg hcalc τ0 δr Ar p hδr hAr q G0 j x hx
        simp only [hd0,map_zero,halfPairing_zero_left,pp_zero_right_local]
    have hrx : IH (V x) = eH i ((Tq δr Ar p q) x) (Uin F0 x) :=
      ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm.rev δr Ar p q F0 hTF i x
    have hd := referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr G0 j x
    have hW := ActualHigherSFormation.referenceWeightedHorizontalAction_inclusion g L q R U x j
      ((hU.differentiable (by simp)) x)
    calc
      _ = PP (IH (UD δr Ar p hδr hAr q G0 j x)) (JL (eH i ((Tq δr Ar p q) x) (Uin F0 x))) := hEP
      _ = PP (IH (UD δr Ar p hδr hAr q G0 j x)) (JL (IH (V x))) :=
        congrArg (fun v : Half => PP (IH (UD δr Ar p hδr hAr q G0 j x)) (JL v)) hrx.symm
      _ = PP (IH (V x)) (JL (IH (UD δr Ar p hδr hAr q G0 j x))) := halfPairing_inclusion_symm _ _
      _ = _ := congrArg (fun v : Neg => PP (IH (V x)) v) ((congrArg (fun v : Half => JL v) hd).trans hW)
  have hL := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (fun x =>
    congrArg (fun z : ℝ => referenceDensityFamily g L (q,x) * c0 x * z) (hpt x)))
  exact hL.trans hG


/-- Scalar zero-order rows use the genuine E/e pivot; this applies to f, Γ and b
coefficients with their original indices, without assuming Q is symmetric. -/
private lemma zero_order_physical_row (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) (k : Fin 3)
    (c0 : R3 → ℝ) (x : R3) :
    referenceDensityFamily g L (q,x) * c0 x * PP (IH (Uin F0 x))
      (JL (IH (VF δr Ar p q hreg δ0 W G0 k x))) =
      PP (IH (Uin G0 x)) (JL ((referenceDensityFamily g L (q,x) * c0 x) •
        eH k ((Tq δr Ar p q) x) (Uin F0 x))) := by
  have hep : PP (IH (Uin F0 x)) (JL (IH (VF δr Ar p q hreg δ0 W G0 k x))) =
      PP (IH (Uin G0 x)) (JL (eH k ((Tq δr Ar p q) x) (Uin F0 x))) := by
    by_cases hx : x ∈ TS G0
    · have hv := ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData
        hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG k x
      exact ((congrArg (fun v : Half => PP (IH (Uin F0 x)) (JL v)) hv).trans
        (halfPairing_inclusion_symm _ _)).trans
        (Cm.pivot k _ (hTG x hx) (Uin G0 x) (Uin F0 x))
    · have hu0 := ActualReverseEHigherLift.revInput_eq_zero hO hD G0 x hx
      have hv0 := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData
        hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W G0 k x hx
      simp only [hu0,hv0,map_zero,pp_zero_right_local,halfPairing_zero_left]
  have hs : PP (IH (Uin G0 x)) (JL ((referenceDensityFamily g L (q,x) * c0 x) •
      eH k ((Tq δr Ar p q) x) (Uin F0 x))) =
      (referenceDensityFamily g L (q,x) * c0 x) *
        PP (IH (Uin G0 x)) (JL (eH k ((Tq δr Ar p q) x) (Uin F0 x))) :=
    (congrArg (fun v : Neg => PP (IH (Uin G0 x)) v)
      (map_smul JL (referenceDensityFamily g L (q,x) * c0 x)
        (eH k ((Tq δr Ar p q) x) (Uin F0 x)))).trans (halfPairing_smul_right _ _ _)
  exact (congrArg (fun v : ℝ => referenceDensityFamily g L (q,x) * c0 x * v) hep).trans hs.symm


/-- Internal integrability for a continuous Half field against a finite compact test.
Only the original continuous scalar coefficient and original volume are used. -/
private lemma integrable_core_pairing (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 : R3 → ℝ) (hc0 : Continuous c0)
    (V : R3 → Half) (hV : Continuous V) :
    Integrable (fun x => c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x))) := by
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  exact ActualHigherSIntegratedPairing.integrable_pp
    (tsupport (F0 : R3 → SphereL2)) F0.property.2.1 c0
    (fun x => IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (fun x => JL (V x))
    hc0 ((IH).continuous.comp hU.continuous) ((JL).continuous.comp hV)
    (fun x hx => Or.inl ((congrArg (fun u : Hi => IH u)
      (ActualReverseEHigherLift.revInput_eq_zero hO hD F0 x hx)).trans (map_zero IH)))

private lemma integral_core_pairing_sum {ι : Type*} [Fintype ι]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 : R3 → ℝ) (hc0 : Continuous c0)
    (V : ι → R3 → Half) (hV : ∀ i, Continuous (V i)) :
    (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (∑ i, V i x))) =
      ∑ i, ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V i x)) := by
  have hpt (x : R3) : c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (∑ i, V i x)) =
      ∑ i, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V i x)) := by
    simp only [map_sum,sphereSobolevDualPairing,inner_sum,Finset.mul_sum]
  calc
    _ = ∫ x, ∑ i, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V i x)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = _ := integral_finset_sum _ (fun i _ => integrable_core_pairing hO hD F0 c0 hc0 (V i) (hV i))

private lemma integral_core_pairing_add (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 : R3 → ℝ) (hc0 : Continuous c0)
    (V W : R3 → Half) (hV : Continuous V) (hW : Continuous W) :
    (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x+W x))) =
      (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x))) +
      ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (W x)) := by
  calc
    _ = ∫ x, (c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x)) +
        c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (W x))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by simp only [map_add,halfPairing_add_right,mul_add])
    _ = _ := integral_add (integrable_core_pairing hO hD F0 c0 hc0 V hV)
      (integrable_core_pairing hO hD F0 c0 hc0 W hW)

private lemma integral_core_pairing_sub (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 : R3 → ℝ) (hc0 : Continuous c0)
    (V W : R3 → Half) (hV : Continuous V) (hW : Continuous W) :
    (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x-W x))) =
      (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x))) -
      ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (W x)) := by
  calc
    _ = ∫ x, (c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x)) -
        c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (W x))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by simp only [map_sub,pp_sub_right_local,mul_sub])
    _ = _ := integral_sub (integrable_core_pairing hO hD F0 c0 hc0 V hV)
      (integrable_core_pairing hO hD F0 c0 hc0 W hW)

private lemma integral_core_pairing_smul (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 σ : R3 → ℝ) (V : R3 → Half) :
    (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (σ x • V x))) =
      ∫ x, (c0 x * σ x) * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x)) := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hp : PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (σ x • V x)) =
      σ x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x)) :=
    (congrArg (fun v : Neg => PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) v)
      (map_smul JL (σ x) (V x))).trans (halfPairing_smul_right _ _ _)
  exact (congrArg (fun v : ℝ => c0 x * v) hp).trans (mul_assoc _ _ _).symm


private lemma contDiff_densityHorizontalReverse (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (R c0 : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (hr : ∀ x, R x ≠ 0)
    (hc0 : ContDiff ℝ ∞ c0) (u : R3 → Hi) (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => densityHorizontalReverse g L q R c0 u i x) := by
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ (fun x => referenceRadiusHorizontalLogDerivative g L q R x i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,x) i hR.contDiffAt (hr x)).comp x
        (contDiffAt_const.prodMk contDiffAt_id))
  have hD : ContDiff ℝ ∞ (fun x => referenceHighWeightedHorizontalAction g L q R u x i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      contDiffAt_referenceHighWeightedHorizontalAction g hg L q R u x i hR.contDiffAt (hr x) hu.contDiffAt)
  have hB : ContDiff ℝ ∞ (fun x => (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x) : Half)) :=
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)).contDiff.comp hu
  have hI : ContDiff ℝ ∞ (fun x => IH (u x)) := (IH).contDiff.comp hu
  have hdc := contDiff_densityDerivativeCoefficient g hg L q i c0 hc0
  have htwo := (show ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ)) from contDiff_const).mul ((hmu.mul hc0).mul hf)
  unfold densityHorizontalReverse
  exact ((((hmu.mul hc0).neg.smul hD).add (htwo.smul hB)).sub (hdc.smul hI))

private lemma contDiff_reverseFirstDerivativeRow (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (c0 : R3 → ℝ) (hc0 : ContDiff ℝ ∞ c0) (i j : Fin 3)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (R1 δr Ar p hδr hAr q c0 i j F0) := by
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ (fun x => referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg (referenceRadius δr Ar p L) (q,x) i
        hR.contDiffAt (ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr))).comp x
        (contDiffAt_const.prodMk contDiffAt_id))
  have hU := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUB := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)
  have hUD : ContDiff ℝ ∞ (UD δr Ar p hδr hAr q F0 i) :=
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (coreReferenceInput hO hD g hg L q δr Ar p i hδr hAr F0)
  have hU0 := ActualReverseEHigherLift.revInput_eq_zero hO hD F0
  have hUB0 := ActualReverseEHigherLift.revDegreeInput_eq_zero hO hD F0
  have hUD0 := ActualHigherSFormation.higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0 i
  have he0 := ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
    (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (Uin F0) hU hU0
  have heB := ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
    (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (UB F0) hUB hUB0
  have heD := ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
    (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (UD δr Ar p hδr hAr q F0 i) hUD hUD0
  have hdc := contDiff_densityDerivativeCoefficient g hg L q i c0 hc0
  have htwo := (show ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ)) from contDiff_const).mul ((hmu.mul hc0).mul hf)
  exact ((((hmu.mul hc0).neg.smul heD).add (htwo.smul heB)).sub (hdc.smul he0))


/-- Internal finite linearity for the exact four Second-row pieces and drift.
All integrability is discharged from continuous fields and the finite compact test. -/
private lemma integral_core_second_block (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (c0 : R3 → ℝ) (hc0 : Continuous c0)
    (V1 V2 V3 : Fin 3 → Fin 3 → R3 → Half)
    (V4 : Fin 3 → Fin 3 → Fin 3 → R3 → Half) (V5 : Fin 3 → R3 → Half)
    (h1 : ∀ i j, Continuous (V1 i j)) (h2 : ∀ i j, Continuous (V2 i j))
    (h3 : ∀ i j, Continuous (V3 i j)) (h4 : ∀ i j k, Continuous (V4 i j k))
    (h5 : ∀ i, Continuous (V5 i)) :
    (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x))
      (JL ((∑ i : Fin 3, ∑ j : Fin 3,
        (V1 i j x + V2 i j x + V3 i j x - ∑ k : Fin 3, V4 i j k x)) +
        ∑ i : Fin 3, V5 i x))) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ((∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V1 i j x))) +
         (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V2 i j x))) +
         (∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V3 i j x))) -
         ∑ k : Fin 3, ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V4 i j k x)))) +
      ∑ i : Fin 3, ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V5 i x)) := by
  let ell : (R3 → Half) → ℝ := fun V =>
    ∫ x, c0 x * PP (IH (ActualHigherSFormation.higherSInput hO hD F0 x)) (JL (V x))
  let row : Fin 3 → Fin 3 → R3 → Half := fun i j x =>
    V1 i j x + V2 i j x + V3 i j x - ∑ k : Fin 3, V4 i j k x
  let rows : R3 → Half := fun x => ∑ i : Fin 3, ∑ j : Fin 3, row i j x
  let drift : R3 → Half := fun x => ∑ i : Fin 3, V5 i x
  have hsum4 (i j : Fin 3) : Continuous (fun x => ∑ k : Fin 3, V4 i j k x) :=
    continuous_finsetSum _ (fun k _ => h4 i j k)
  have hrow (i j : Fin 3) : Continuous (row i j) :=
    (((h1 i j).add (h2 i j)).add (h3 i j)).sub (hsum4 i j)
  have hinner (i : Fin 3) : Continuous (fun x => ∑ j : Fin 3, row i j x) :=
    continuous_finsetSum _ (fun j _ => hrow i j)
  have hrows : Continuous rows := continuous_finsetSum _ (fun i _ => hinner i)
  have hdrift : Continuous drift := continuous_finsetSum _ (fun i _ => h5 i)
  have hrowIntegral (i j : Fin 3) : ell (row i j) =
      ell (V1 i j) + ell (V2 i j) + ell (V3 i j) - ∑ k : Fin 3, ell (V4 i j k) := by
    have h12 : ell (fun x => V1 i j x+V2 i j x) = ell (V1 i j)+ell (V2 i j) :=
      integral_core_pairing_add hO hD F0 c0 hc0 (V1 i j) (V2 i j) (h1 i j) (h2 i j)
    have h123 : ell (fun x => V1 i j x+V2 i j x+V3 i j x) =
        ell (V1 i j)+ell (V2 i j)+ell (V3 i j) :=
      (integral_core_pairing_add hO hD F0 c0 hc0 (fun x => V1 i j x+V2 i j x) (V3 i j)
        ((h1 i j).add (h2 i j)) (h3 i j)).trans
        (congrArg (fun z : ℝ => z+ell (V3 i j)) h12)
    have h4sum : ell (fun x => ∑ k : Fin 3, V4 i j k x) = ∑ k : Fin 3, ell (V4 i j k) :=
      integral_core_pairing_sum hO hD F0 c0 hc0 (V4 i j) (h4 i j)
    exact (integral_core_pairing_sub hO hD F0 c0 hc0
      (fun x => V1 i j x+V2 i j x+V3 i j x) (fun x => ∑ k : Fin 3, V4 i j k x)
      (((h1 i j).add (h2 i j)).add (h3 i j)) (hsum4 i j)).trans
      (congrArg₂ (fun a b : ℝ => a-b) h123 h4sum)
  have hrowOuter : ell rows = ∑ i : Fin 3, ell (fun x => ∑ j : Fin 3, row i j x) :=
    integral_core_pairing_sum hO hD F0 c0 hc0 (fun i x => ∑ j : Fin 3, row i j x) hinner
  have hrowInner : (∑ i : Fin 3, ell (fun x => ∑ j : Fin 3, row i j x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ell (row i j) :=
    Finset.sum_congr rfl (fun i _ => integral_core_pairing_sum hO hD F0 c0 hc0 (row i) (hrow i))
  have hrowValues : (∑ i : Fin 3, ∑ j : Fin 3, ell (row i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (ell (V1 i j)+ell (V2 i j)+ell (V3 i j)-∑ k : Fin 3, ell (V4 i j k)) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hrowIntegral i j))
  have hrowsTotal := hrowOuter.trans (hrowInner.trans hrowValues)
  have hdriftIntegral : ell drift = ∑ i : Fin 3, ell (V5 i) :=
    integral_core_pairing_sum hO hD F0 c0 hc0 V5 h5
  exact (integral_core_pairing_add hO hD F0 c0 hc0 rows drift hrows hdrift).trans
    (congrArg₂ (fun a b : ℝ => a+b) hrowsTotal hdriftIntegral)


local notation "FS" => ActualHigherSFormation.higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Literal split of the unchanged forward Second field into the checked rows. -/
private lemma forwardSecond_literal_split (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (G0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let R := referenceRadius δr Ar p L
    let cij := secondCoefficient g g2 L q δr Ar p
    let fi := referenceRadiusHorizontalLogDerivative g L q R x
    let Γ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j
    FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x =
      (∑ i : Fin 3, ∑ j : Fin 3,
        (cij i j x • referenceHighWeightedHorizontalAction g L q R
            (VF δr Ar p q hreg δ0 W G0 j) x i +
         cij i j x • EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x) +
         (cij i j x * fi i) • IH (VF δr Ar p q hreg δ0 W G0 j x) -
         ∑ k : Fin 3, (cij i j x * Γ i j k) • IH (VF δr Ar p q hreg δ0 W G0 k x))) +
      ∑ i : Fin 3, ((R x)^2 * normalizedSecondDriftFrameJoint g g2 L i (q,x)) •
        IH (VF δr Ar p q hreg δ0 W G0 i x) := by
  dsimp only
  simp only [ActualHigherSFormation.higherSSecondHalf,ActualHigherSFormation.higherSSecondWordHalf,
    Finset.smul_sum,smul_add,smul_sub,smul_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    secondCoefficient,mul_assoc]

/-- Literal split of the already formed reverse density field into the same rows,
with scalar association made explicit. -/
private lemma reverseSecond_literal_split (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let R := referenceRadius δr Ar p L
    let cij := secondCoefficient g g2 L q δr Ar p
    let μ := referenceDensityFamily g L (q,x)
    let fi := referenceRadiusHorizontalLogDerivative g L q R x
    let Γ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j
    RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x =
      (∑ i : Fin 3, ∑ j : Fin 3,
        (R1 δr Ar p hδr hAr q (cij i j) i j F0 x +
         densityHorizontalReverse g L q R (cij i j) (VR hreg δ0 W δr Ar p q F0 i) j x +
         (μ * (cij i j x * fi i)) • eH j ((Tq δr Ar p q) x) (Uin F0 x) -
         ∑ k : Fin 3, (μ * (cij i j x * Γ i j k)) • eH k ((Tq δr Ar p q) x) (Uin F0 x))) +
      ∑ i : Fin 3, (μ * ((R x)^2 * normalizedSecondDriftFrameJoint g g2 L i (q,x))) •
        eH i ((Tq δr Ar p q) x) (Uin F0 x) := by
  unfold revSecondDensityHalf reverseFirstDerivativeRow densityHorizontalReverse
  dsimp only
  simp only [mul_assoc]


/-- Full exact Second-block adjoint for independent finite test/input cores.
Every coefficient derivative, divergence, physical degree correction, Γ and b term
is present. Both integral existence claims use the original physical volume. -/
theorem integrated_second_dual_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) * PP (IH (Uin F0 x))
      (JL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x))) ∧
    Integrable (fun x => PP (IH (Uin G0 x)) (JL (RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x))) ∧
    (∫ x, referenceDensityFamily g L (q,x) * PP (IH (Uin F0 x))
      (JL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x))) =
      ∫ x, PP (IH (Uin G0 x)) (JL (RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x)) := by
  let R := referenceRadius δr Ar p L
  let μ : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let cij := secondCoefficient g g2 L q δr Ar p
  let fi : Fin 3 → R3 → ℝ := fun i x => referenceRadiusHorizontalLogDerivative g L q R x i
  let Γ : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j k x =>
    referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j
  let bi : Fin 3 → R3 → ℝ := fun i x => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let V := VF δr Ar p q hreg δ0 W G0
  let Z := VR hreg δ0 W δr Ar p q F0
  let eF : Fin 3 → R3 → Half := fun k x => eH k ((Tq δr Ar p q) x) (Uin F0 x)
  let X1 : Fin 3 → Fin 3 → R3 → Half := fun i j x =>
    cij i j x • referenceHighWeightedHorizontalAction g L q R (V j) x i
  let X2 : Fin 3 → Fin 3 → R3 → Half := fun i j x =>
    cij i j x • EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x)
  let X3 : Fin 3 → Fin 3 → R3 → Half := fun i j x => (cij i j x * fi i x) • IH (V j x)
  let X4 : Fin 3 → Fin 3 → Fin 3 → R3 → Half := fun i j k x =>
    (cij i j x * Γ i j k x) • IH (V k x)
  let X5 : Fin 3 → R3 → Half := fun i x => ((R x)^2 * bi i x) • IH (V i x)
  let Y1 : Fin 3 → Fin 3 → R3 → Half := fun i j => R1 δr Ar p hδr hAr q (cij i j) i j F0
  let Y2 : Fin 3 → Fin 3 → R3 → Half := fun i j x =>
    densityHorizontalReverse g L q R (cij i j) (Z i) j x
  let Y3 : Fin 3 → Fin 3 → R3 → Half := fun i j x => (μ x * (cij i j x * fi i x)) • eF j x
  let Y4 : Fin 3 → Fin 3 → Fin 3 → R3 → Half := fun i j k x => (μ x * (cij i j x * Γ i j k x)) • eF k x
  let Y5 : Fin 3 → R3 → Half := fun i x => (μ x * ((R x)^2 * bi i x)) • eF i x
  let ellL : (R3 → Half) → ℝ := fun V0 => ∫ x, μ x * PP (IH (Uin F0 x)) (JL (V0 x))
  let ellR : (R3 → Half) → ℝ := fun V0 => ∫ x, PP (IH (Uin G0 x)) (JL (V0 x))
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr (x : R3) : R x ≠ 0 := ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hmu : ContDiff ℝ ∞ μ :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hcij (i j : Fin 3) := contDiff_secondCoefficient g g2 hg hg2 L q δr Ar p hδr hAr i j
  have hf (i : Fin 3) : ContDiff ℝ ∞ (fi i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,x) i hR.contDiffAt (hr x)).comp x
        (contDiffAt_const.prodMk contDiffAt_id))
  have hΓ (i j k : Fin 3) : ContDiff ℝ ∞ (Γ i j k) :=
    ActualHigherSFormation.contDiff_referenceGramConnectionSlice g hg L q i j k
  have hb (i : Fin 3) : ContDiff ℝ ∞ (bi i) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp (contDiff_const.prodMk contDiff_id)
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hV (j : Fin 3) : ContDiff ℝ ∞ (V j) :=
    ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG j
  have hIV (j : Fin 3) : ContDiff ℝ ∞ (fun x => IH (V j x)) := (IH).contDiff.comp (hV j)
  have hDV (i j : Fin 3) : ContDiff ℝ ∞ (fun x => referenceHighWeightedHorizontalAction g L q R (V j) x i) :=
    contDiff_iff_contDiffAt.2 (fun x =>
      contDiffAt_referenceHighWeightedHorizontalAction g hg L q R (V j) x i hR.contDiffAt (hr x) (hV j).contDiffAt)
  have hUD (j : Fin 3) : ContDiff ℝ ∞ (UD δr Ar p hδr hAr q G0 j) :=
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreReferenceInput hO hD g hg L q δr Ar p j hδr hAr G0)
  have hUD0 (j : Fin 3) := ActualHigherSFormation.higherSReferenceInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q G0 j
  have hED (i j : Fin 3) : ContDiff ℝ ∞ (fun x => EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (EH i) G0
      (fun x hx => Cm.germHigh i _ (hTG x hx)) (UD δr Ar p hδr hAr q G0 j) (hUD j) (hUD0 j)
  have hUF := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hUF0 := ActualReverseEHigherLift.revInput_eq_zero hO hD F0
  have heF (k : Fin 3) : ContDiff ℝ ∞ (eF k) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH k) F0
      (fun x hx => Cm.rev.germHigh k _ (hTF x hx)) (Uin F0) hUF hUF0
  have hZ (i : Fin 3) : ContDiff ℝ ∞ (Z i) :=
    ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hTF i
  have hX1 (i j : Fin 3) : Continuous (X1 i j) := ((hcij i j).smul (hDV i j)).continuous
  have hX2 (i j : Fin 3) : Continuous (X2 i j) := ((hcij i j).smul (hED i j)).continuous
  have hX3 (i j : Fin 3) : Continuous (X3 i j) := (((hcij i j).mul (hf i)).smul (hIV j)).continuous
  have hX4 (i j k : Fin 3) : Continuous (X4 i j k) := (((hcij i j).mul (hΓ i j k)).smul (hIV k)).continuous
  have hX5 (i : Fin 3) : Continuous (X5 i) := (((hR.pow 2).mul (hb i)).smul (hIV i)).continuous
  have hY1 (i j : Fin 3) : Continuous (Y1 i j) :=
    (contDiff_reverseFirstDerivativeRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm δr Ar p hδr hAr q (cij i j) (hcij i j) i j F0 hTF).continuous
  have hY2 (i j : Fin 3) : Continuous (Y2 i j) :=
    (contDiff_densityHorizontalReverse g hg L q R (cij i j) hR hr (hcij i j) (Z i) (hZ i) j).continuous
  have hY3 (i j : Fin 3) : Continuous (Y3 i j) := ((hmu.mul ((hcij i j).mul (hf i))).smul (heF j)).continuous
  have hY4 (i j k : Fin 3) : Continuous (Y4 i j k) := ((hmu.mul ((hcij i j).mul (hΓ i j k))).smul (heF k)).continuous
  have hY5 (i : Fin 3) : Continuous (Y5 i) := ((hmu.mul ((hR.pow 2).mul (hb i))).smul (heF i)).continuous
  have hFSeq : FS δr Ar p hδr hAr q hreg δ0 W g2 G0 = fun x =>
      (∑ i : Fin 3, ∑ j : Fin 3, (X1 i j x+X2 i j x+X3 i j x-∑ k : Fin 3, X4 i j k x)) +
      ∑ i : Fin 3, X5 i x :=
    funext (fun x => forwardSecond_literal_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q G0 x)
  have hRDSeq : RD hreg δ0 W g2 δr Ar p hδr hAr q F0 = fun x =>
      (∑ i : Fin 3, ∑ j : Fin 3, (Y1 i j x+Y2 i j x+Y3 i j x-∑ k : Fin 3, Y4 i j k x)) +
      ∑ i : Fin 3, Y5 i x :=
    funext (fun x => reverseSecond_literal_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
  have hLBlock := integral_core_second_block hO hD F0 μ hmu.continuous X1 X2 X3 X4 X5 hX1 hX2 hX3 hX4 hX5
  have hRBlockRaw := integral_core_second_block hO hD G0 (fun _ => (1 : ℝ)) continuous_const
    Y1 Y2 Y3 Y4 Y5 hY1 hY2 hY3 hY4 hY5
  have hL : ellL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0) =
      (∑ i : Fin 3, ∑ j : Fin 3, (ellL (X1 i j)+ellL (X2 i j)+ellL (X3 i j)-∑ k : Fin 3, ellL (X4 i j k))) +
      ∑ i : Fin 3, ellL (X5 i) := (congrArg ellL hFSeq).trans hLBlock
  have hRBlock : ellR (fun x =>
      (∑ i : Fin 3, ∑ j : Fin 3, (Y1 i j x+Y2 i j x+Y3 i j x-∑ k : Fin 3, Y4 i j k x)) +
      ∑ i : Fin 3, Y5 i x) =
      (∑ i : Fin 3, ∑ j : Fin 3, (ellR (Y1 i j)+ellR (Y2 i j)+ellR (Y3 i j)-∑ k : Fin 3, ellR (Y4 i j k))) +
      ∑ i : Fin 3, ellR (Y5 i) := by simpa only [one_mul] using hRBlockRaw
  have hRR := (congrArg ellR hRDSeq).trans hRBlock
  have hrow1 (i j : Fin 3) : ellL (X1 i j) = ellR (Y1 i j) :=
    (integral_core_pairing_smul hO hD F0 μ (cij i j)
      (fun x => referenceHighWeightedHorizontalAction g L q R (V j) x i)).trans
      (integrated_first_derivative_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm δr Ar p hδr hAr q (cij i j) (hcij i j) i j F0 G0 hTG)
  have hrow2 (i j : Fin 3) : ellL (X2 i j) = ellR (Y2 i j) :=
    (integral_core_pairing_smul hO hD F0 μ (cij i j)
      (fun x => EH i ((Tq δr Ar p q) x) (UD δr Ar p hδr hAr q G0 j x))).trans
      (integrated_second_derivative_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm δr Ar p hδr hAr q (cij i j) (hcij i j) i j F0 G0 hTF hTG)
  have hzero (k : Fin 3) (σ : R3 → ℝ) : ellL (fun x => σ x • IH (V k x)) =
      ellR (fun x => (μ x*σ x) • eF k x) :=
    (integral_core_pairing_smul hO hD F0 μ σ (fun x => IH (V k x))).trans
      (integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (fun x =>
        zero_order_physical_row g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg δ0 W δ Cm δr Ar p hδr hAr q F0 G0 hTG k σ x)))
  have hrow3 (i j : Fin 3) : ellL (X3 i j) = ellR (Y3 i j) := hzero j (fun x => cij i j x*fi i x)
  have hrow4 (i j k : Fin 3) : ellL (X4 i j k) = ellR (Y4 i j k) := hzero k (fun x => cij i j x*Γ i j k x)
  have hrow5 (i : Fin 3) : ellL (X5 i) = ellR (Y5 i) := hzero i (fun x => (R x)^2*bi i x)
  have hrow (i j : Fin 3) :
      ellL (X1 i j)+ellL (X2 i j)+ellL (X3 i j)-(∑ k : Fin 3, ellL (X4 i j k)) =
      ellR (Y1 i j)+ellR (Y2 i j)+ellR (Y3 i j)-(∑ k : Fin 3, ellR (Y4 i j k)) := congrArg₂ (fun a b : ℝ => a-b)
    (congrArg₂ (fun a b : ℝ => a+b) (congrArg₂ (fun a b : ℝ => a+b) (hrow1 i j) (hrow2 i j)) (hrow3 i j))
    (Finset.sum_congr rfl (fun k _ => hrow4 i j k))
  have hmid :
      (∑ i : Fin 3, ∑ j : Fin 3, (ellL (X1 i j)+ellL (X2 i j)+ellL (X3 i j)-∑ k : Fin 3, ellL (X4 i j k))) +
        (∑ i : Fin 3, ellL (X5 i)) =
      (∑ i : Fin 3, ∑ j : Fin 3, (ellR (Y1 i j)+ellR (Y2 i j)+ellR (Y3 i j)-∑ k : Fin 3, ellR (Y4 i j k))) +
        (∑ i : Fin 3, ellR (Y5 i)) := congrArg₂ (fun a b : ℝ => a+b)
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hrow i j)))
    (Finset.sum_congr rfl (fun i _ => hrow5 i))
  have hEq := hL.trans (hmid.trans hRR.symm)
  have hrowCont (i j : Fin 3) : Continuous (fun x => X1 i j x+X2 i j x+X3 i j x-∑ k : Fin 3, X4 i j k x) :=
    (((hX1 i j).add (hX2 i j)).add (hX3 i j)).sub (continuous_finsetSum _ (fun k _ => hX4 i j k))
  have hFSplitCont : Continuous (fun x =>
      (∑ i : Fin 3, ∑ j : Fin 3, (X1 i j x+X2 i j x+X3 i j x-∑ k : Fin 3, X4 i j k x)) +∑ i : Fin 3, X5 i x) :=
    (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => hrowCont i j))).add
      (continuous_finsetSum _ (fun i _ => hX5 i))
  have hFScont : Continuous (FS δr Ar p hδr hAr q hreg δ0 W g2 G0) := hFSeq.symm ▸ hFSplitCont
  have hRDcont := (contDiff_revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF).continuous
  refine ⟨integrable_core_pairing hO hD F0 μ hmu.continuous _ hFScont,?_,hEq⟩
  simpa only [one_mul] using integrable_core_pairing hO hD G0 (fun _ => (1 : ℝ)) continuous_const _ hRDcont


local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- Full actual physical Second-block adjoint in the original positive density,
with the normalized Half output, independent finite inputs and both integrability claims. -/
theorem integrated_second_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x,KL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪KL (RH hreg δ0 W g2 δr Ar p hδr hAr q F0 x),G0.val x⟫_ℝ) ∧
    (∫ x, referenceDensityFamily g L (q,x) *
      ⟪F0.val x,KL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) *
        ⟪KL (RH hreg δ0 W g2 δr Ar p hδr hAr q F0 x),G0.val x⟫_ℝ := by
  have hd := integrated_second_dual_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hFval (x : R3) : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  have hGval (x : R3) : G0.val x = KL (IH (Uin G0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD G0 x).symm
  have hLpt (x : R3) : referenceDensityFamily g L (q,x) * PP (IH (Uin F0 x))
      (JL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)) =
      referenceDensityFamily g L (q,x) * ⟪F0.val x,KL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)⟫_ℝ := by
    have hp := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
      (IH (Uin F0 x)) (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)
    have hf := congrArg (fun v : SphereL2 => ⟪v,KL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)⟫_ℝ) (hFval x).symm
    exact congrArg (fun v : ℝ => referenceDensityFamily g L (q,x)*v) (hp.trans hf)
  have hRpt (x : R3) : PP (IH (Uin G0 x)) (JL (RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x)) =
      referenceDensityFamily g L (q,x) * ⟪KL (RH hreg δ0 W g2 δr Ar p hδr hAr q F0 x),G0.val x⟫_ℝ := by
    have hp := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
      (IH (Uin G0 x)) (RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
    have hg0 := congrArg (fun v : SphereL2 => ⟪KL (RD hreg δ0 W g2 δr Ar p hδr hAr q F0 x),v⟫_ℝ) (hGval x).symm
    have hden := congrArg (fun v : Half => ⟪KL v,G0.val x⟫_ℝ)
      (density_mul_revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p hδr hAr q F0 x)
    have hscale := (congrArg (fun v : SphereL2 => ⟪v,G0.val x⟫_ℝ)
      (map_smul KL (referenceDensityFamily g L (q,x))
        (RH hreg δ0 W g2 δr Ar p hδr hAr q F0 x))).trans
      (real_inner_smul_left _ _ _)
    exact hp.trans ((real_inner_comm _ _).trans (hg0.trans (hden.symm.trans hscale)))
  have hLI := hd.1.congr (Filter.Eventually.of_forall hLpt)
  have hRI := hd.2.1.congr (Filter.Eventually.of_forall hRpt)
  have hLEq := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hLpt)
  have hREq := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hRpt)
  exact ⟨hLI,hRI,hLEq.symm.trans (hd.2.2.trans hREq)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSecondAdjoint
