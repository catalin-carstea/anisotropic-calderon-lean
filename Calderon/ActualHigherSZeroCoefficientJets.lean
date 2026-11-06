/- Opus v088: canonical zero-base HigherS coefficient, value equality, global
supported field identity and its iterated derivatives.  Source-only, author has
NOT compiled.  The germ and two-jet bounds are stated as EXACT targets (Prop
definitions) and are NOT proved here; see MATHEMATICS.md §4 and STATUS.md. -/
import Calderon.ActualHigherSFirstCoefficientJets
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientJets
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  -- the remaining opens of `ActualHigherSFormation`, where the log-derivative germ
  -- `contDiffAt_referenceRadiusHorizontalLogDerivative` is used unqualified
  ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualGeneratorEHighGainedGraph ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/- Root repair: cache the identical inferred inner operator instances before its Frechet derivative. -/
@[instance_reducible] private def highHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highHalfNormed
@[instance_reducible] private def highHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highHalfSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => ActualHigherSCoefficientExtraction.profileLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BCC" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "SN" => ActualHigherSFormation.nativeHigherSNegative
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ

/-- The EXACT original zero-coefficient formula, with the lower family `El`
displayed as a parameter.  The differentiated ordinary `profileHigh` inside
`secondZeroRow`, both Q orders and all composition orders are those of
`higherSZeroCoefficient`. -/
def zeroCoefficientWith (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (x : R3) : Hi →L[ℝ] Neg :=
  ActualHigherSCoefficientExtraction.zeroCoefficient (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
      (PH δr Ar p q) El x)
    (fun j => PH δr Ar p q j x) El
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))

lemma higherSZeroCoefficient_eq_with (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    CZ g2 δr Ar p q x =
      zeroCoefficientWith g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 δr Ar p q (PL δr Ar p q x) x := rfl

/-- Canonical zero coefficient: the original moving `profileLow` is replaced by
`canonicalLow (higherSParam x)` BEFORE any ambient differentiation.  The actual
differentiated canonical `profileHigh` is retained. -/
def canonicalZeroCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) : Hi →L[ℝ] Neg :=
  zeroCoefficientWith g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 δr Ar p q (fun j => EL j ((Tq δr Ar p q) x)) x
local notation "CZc" => canonicalZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Coefficient VALUE equality on the native room (pointwise only). -/
theorem canonicalZeroCoefficient_eq_original_at_room
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    CZc g2 δr Ar p q x = CZ g2 δr Ar p q x := by
  have heq (j : Fin 3) := ActualHigherSCoefficientBounds.profileLow_eq_canonical
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    δr Ar p hδr hAr q hq x hx j
  have hfun : PL δr Ar p q x = (fun j => EL j ((Tq δr Ar p q) x)) := funext heq
  exact (congrArg (fun El : Fin 3 → Half →L[ℝ] Neg =>
    zeroCoefficientWith g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 δr Ar p q El x) hfun).symm

/-- Pointwise agreement of the two coefficients APPLIED to the supported input,
on all of R3 (off the support the input vanishes). -/
lemma zero_terms_agree_everywhere
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    CZ g2 δr Ar p q x (UF F x) = CZc g2 δr Ar p q x (UF F x) := by
  by_cases hx : x ∈ tsupport F.val
  · exact (congrArg (fun A : Hi →L[ℝ] Neg => A (UF F x))
      (canonicalZeroCoefficient_eq_original_at_room g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq x (hTF x hx))).symm
  · have hu := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q F x hx
    rw [hu, map_zero, map_zero]

/-- GLOBAL supported field identity: the WHOLE negative HigherS field equals the
canonical first-coefficient field plus the canonical zero-coefficient field, as
functions on all of R3, with support-only room membership and no finite-output
assumption. -/
theorem actual_higherS_canonical_zero_field
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (fun x => SN g2 q (referenceRadius δr Ar p L) (UF F) x) =
      (fun x => (∑ l : Fin 3, BCC g2 δr Ar p q x l
        (IH (fderiv ℝ (UF F) x (coordinateDirection l)))) + CZc g2 δr Ar p q x (UF F x)) := by
  have h1 := ActualHigherSFirstCoefficientJets.actual_higherS_canonical_coordinate_field
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 δr Ar p hδr hAr q hq F hTF
  funext x
  have hz := zero_terms_agree_everywhere g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F hTF x
  exact (congrFun h1 x).trans (congrArg (fun z : Neg => (∑ l : Fin 3, BCC g2 δr Ar p q x l
    (IH (fderiv ℝ (UF F) x (coordinateDirection l)))) + z) hz)

/-- Equality of iterated Frechet derivatives, justified ONLY by the preceding
whole-field function equality (never by closed-room coefficient agreement). -/
theorem iteratedFDeriv_actual_higherS_canonical_zero_field
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => SN g2 q (referenceRadius δr Ar p L) (UF F) x) =
      iteratedFDeriv ℝ n (fun x => (∑ l : Fin 3, BCC g2 δr Ar p q x l
        (IH (fderiv ℝ (UF F) x (coordinateDirection l)))) + CZc g2 δr Ar p q x (UF F x)) :=
  congrArg (iteratedFDeriv ℝ n) (actual_higherS_canonical_zero_field
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 δr Ar p hδr hAr q hq F hTF)

/-- Genuine C^∞ germ of the PHYSICAL derivative of the canonical `profileHigh`
(the new ingredient of the zero coefficient), from the same common room. -/
theorem contDiffAt_fderiv_profileHigh (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (fderiv ℝ (PH δr Ar p q j)) x := by
  have ht := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q
  have hPH : ContDiffAt ℝ ∞ (PH δr Ar p q j) x :=
    (Cm.germHigh j _ hx).comp x ht.contDiffAt
  exact hPH.fderiv_right (m := ∞) (by simp)

local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)

/-- Generic germ rule for the original finite zero-coefficient assembly. -/
lemma contDiffAt_zeroCoefficient_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : E → ℝ) (Q : E → Fin 3 → Fin 3 → ℝ) (b : E → Fin 3 → ℝ)
    (Z : E → Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : E → Fin 3 → Hi →L[ℝ] Half)
    (El : E → Fin 3 → Half →L[ℝ] Neg) (Alo : Fin 3 → Half →L[ℝ] Neg)
    (Ahi : Fin 3 → Hi →L[ℝ] Half) (x : E)
    (hr : ContDiffAt ℝ ∞ r x) (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun y => Q y i j) x)
    (hb : ∀ i, ContDiffAt ℝ ∞ (fun y => b y i) x)
    (hZ : ∀ i j, ContDiffAt ℝ ∞ (fun y => Z y i j) x)
    (hEh : ∀ j, ContDiffAt ℝ ∞ (fun y => Eh y j) x)
    (hEl : ∀ i, ContDiffAt ℝ ∞ (fun y => El y i) x) :
    ContDiffAt ℝ ∞ (fun y => ActualHigherSCoefficientExtraction.zeroCoefficient
      (r y) (Q y) (b y) (Z y) (Eh y) (El y) Alo Ahi) x := by
  have jl : ContDiffAt ℝ ∞ (fun _ : E => (JL : Half →L[ℝ] Neg)) x := contDiffAt_const
  unfold ActualHigherSCoefficientExtraction.zeroCoefficient
  exact ((((hr.pow 2).smul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (hQ i j).smul (hZ i j))).add
    ((hr.pow 2).smul (ContDiffAt.sum fun i _ => (hb i).smul (jl.clm_comp (hEh i))))).add
    (hr.smul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (hQ i j).smul (((contDiffAt_const (c := Alo i)).clm_comp (hEh j)).add
        ((hEl i).clm_comp (contDiffAt_const (c := Ahi j))))))).add
    ((hr.pow 3).smul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (hQ i j).smul ((hEl i).clm_comp (hEh j))))

/-- Genuine C^∞ GERM in x of the canonical zero coefficient at every point whose
actual profile parameter lies in the native room.  Smoothness facts are those of
the checked `ActualHigherSFormation` block (connection slice, Q, drift, log-derivative). -/
theorem contDiffAt_canonicalZeroCoefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (fun y => CZc g2 δr Ar p q y) x := by
  have hRR : ContDiff ℝ ∞ (referenceRadius δr Ar p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have ht := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have hQ (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x :=
    ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (f := fun y : R3 => (q,y)) hqy).contDiffAt
  have hb (i : Fin 3) : ContDiffAt ℝ ∞
      (fun y => normalizedSecondDriftFrameJoint g g2 L i (q,y)) x :=
    ((contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (f := fun y : R3 => (q,y)) hqy).contDiffAt
  have hX (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i) x :=
    ((contDiff_referenceMetricGramFrame g hg L i).comp (f := fun y : R3 => (q,y)) hqy).contDiffAt
  have hΓ (i j k : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j) x :=
    (ActualHigherSFormation.contDiff_referenceGramConnectionSlice g hg L q i j k).contDiffAt
  have hf (i : Fin 3) : ContDiffAt ℝ ∞
      (fun y => referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i) x :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg (referenceRadius δr Ar p L) (q,x) i
      hRR.contDiffAt (ne_of_gt (referenceRadius_pos δr Ar p L x hδr hAr))).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
  have hOlo (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceLowerHorizontalAngularL g L q y i) x :=
    (contDiff_referenceLowerHorizontalAngularL g hg L q i).contDiffAt
  have hOhi (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceHighHorizontalAngularL g L q y i) x :=
    (contDiff_referenceHighHorizontalAngularL g hg L q i).contDiffAt
  have hEL (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => EL i ((Tq δr Ar p q) y)) x :=
    (Cm.germLow i _ hx).comp x ht.contDiffAt
  have hPH (j : Fin 3) : ContDiffAt ℝ ∞ (fun y => PH δr Ar p q j y) x :=
    (Cm.germHigh j _ hx).comp x ht.contDiffAt
  have hdPH (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (PH δr Ar p q j) y (referenceMetricGramFrame g L (q,y) i)) x :=
    (contDiffAt_fderiv_profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm δr Ar p hδr hAr q j x hx).clm_apply (hX i)
  have jl : ContDiffAt ℝ ∞ (fun _ : R3 => (JL : Half →L[ℝ] Neg)) x := contDiffAt_const
  have hZ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun y =>
      ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
        (PH δr Ar p q) (fun k => EL k ((Tq δr Ar p q) y)) y i j) x := by
    unfold ActualHigherSCoefficientExtraction.secondZeroRow
      ActualHigherSCoefficientExtraction.weightedLowerZero
      ActualHigherSCoefficientExtraction.weightedHighZero
    exact ((((jl.clm_comp (hdPH i j)).add
      (((hOlo i).add ((hf i).smul contDiffAt_const)).clm_comp (hPH j))).add
      ((hEL i).clm_comp ((hOhi j).add ((hf j).smul contDiffAt_const)))).add
      ((hf i).smul (jl.clm_comp (hPH j)))).sub
      (ContDiffAt.sum fun k _ => (hΓ i j k).smul (jl.clm_comp (hPH k)))
  exact contDiffAt_zeroCoefficient_family (referenceRadius δr Ar p L)
    (fun y i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
    (fun y i => normalizedSecondDriftFrameJoint g g2 L i (q,y))
    (fun y => ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
      (PH δr Ar p q) (fun k => EL k ((Tq δr Ar p q) y)) y)
    (fun y j => PH δr Ar p q j y) (fun y k => EL k ((Tq δr Ar p q) y))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)) x
    hRR.contDiffAt hQ hb hZ hPH hEL

/-! ## Exact remaining target (NOT proved in this packet) -/

/-- Exact two-jet target: ONE `K` after the formation room and fixed admissible
`g2`, BEFORE `δr, Ar, p, q, x`, input and angular degree. -/
def CanonicalZeroCoefficientJetTarget (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
    ∀ n : ℕ, n ≤ 2 →
    ‖iteratedFDeriv ℝ n (fun y => CZc g2 δr Ar p q y) x‖ ≤
      K*referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^n

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientJets
