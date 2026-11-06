import Calderon.ActualHigherSSecondAdjoint
import Calderon.ActualHigherSAngularAdjoint
import Calderon.ActualCommonQuadraticFormationConsumer
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointFormation
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "RS" => ActualHigherSSecondAdjoint.revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RA" => ActualHigherSAngularAdjoint.revAngularHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- Exact higher-S adjoint: normalized Second, angular and quadratic reverses,
all evaluated on the SAME retained W and original profile. -/
def higherSAdjointHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  RS hreg δ0 W g2 δr Ar p hδr hAr q F0 x +
    RA hreg δ0 W g2 δr Ar p q F0 x + RD hreg δ0 W g2 δr Ar p q F0 x

/-- Physical SphereL2 output through the original map. -/
def higherSAdjointOut (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  KL (higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q F0 x)

local notation "ADJ" => higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ADJO" => higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Global smoothness of the full higher-S reverse on the same retained room. -/
theorem contDiff_higherSAdjointHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) :=
  ((ActualHigherSSecondAdjoint.contDiff_revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hT).add
    (ActualHigherSAngularAdjoint.contDiff_revAngular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hT)).add
    (ActualCommonFirstWordQuadraticAdjoint.contDiff_revDouble g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hT)

theorem higherSAdjointHalf_eq_zero_off_support (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ TS F0) :
    ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x = 0 := by
  have hs := ActualHigherSSecondAdjoint.revSecondHalf_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q F0 x hx
  have ha := ActualHigherSAngularAdjoint.revAngular_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p q F0 x hx
  have hd := ActualCommonFirstWordQuadraticAdjoint.revDouble_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p q F0 x hx
  simp only [higherSAdjointHalf,hs,ha,hd,add_zero]

theorem tsupport_higherSAdjointHalf_subset (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) :
    tsupport (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) ⊆ TS F0 := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  exact (Function.mem_support.1 hx) (higherSAdjointHalf_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q F0 x h)

theorem hasCompactSupport_higherSAdjointHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) :
    HasCompactSupport (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) :=
  IsCompact.of_isClosed_subset F0.property.2.1 (isClosed_tsupport _)
    (tsupport_higherSAdjointHalf_subset g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0)

theorem contDiff_higherSAdjointOut (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0) :=
  (KL).contDiff.comp (contDiff_higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hT)

private lemma integral_three_adds (A B C : R3 → ℝ)
    (hA : Integrable A) (hB : Integrable B) (hC : Integrable C) :
    (∫ x, A x+B x+C x) = (∫ x, A x)+(∫ x, B x)+∫ x, C x := by
  calc
    _ = (∫ x, A x+B x)+∫ x, C x :=
      integral_add (f := fun x => A x+B x) (g := C) (hA.add hB) hC
    _ = _ := congrArg (fun z : ℝ => z+∫ x, C x) (integral_add (f := A) (g := B) hA hB)

local notation "FS" => ActualHigherSFormation.higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "FA" => ActualHigherSFormation.higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Exact physical adjoint of the entire original HigherS=Second+Angular+Double
block, for independent finite inputs on one common retained W/radius. -/
theorem integrated_higherS_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ) ∧
    (∫ x, referenceDensityFamily g L (q,x) *
      ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) *
        ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ := by
  let μ : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let L1 : R3 → ℝ := fun x => μ x * ⟪F0.val x,KL (FS δr Ar p hδr hAr q hreg δ0 W g2 G0 x)⟫_ℝ
  let L2 : R3 → ℝ := fun x => μ x * ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ
  let L3 : R3 → ℝ := fun x => μ x * ⟪F0.val x,KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ
  let R1 : R3 → ℝ := fun x => μ x * ⟪KL (RS hreg δ0 W g2 δr Ar p hδr hAr q F0 x),G0.val x⟫_ℝ
  let R2 : R3 → ℝ := fun x => μ x * ⟪KL (RA hreg δ0 W g2 δr Ar p q F0 x),G0.val x⟫_ℝ
  let R3f : R3 → ℝ := fun x => μ x * ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x),G0.val x⟫_ℝ
  have hs := ActualHigherSSecondAdjoint.integrated_second_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have ha := ActualHigherSAngularAdjoint.integrated_angular_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hd := ActualCommonFirstWordQuadraticAdjoint.integrated_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hLpt (x : R3) : μ x * ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ =
      L1 x+L2 x+L3 x := by
    dsimp only [L1,L2,L3]
    unfold ActualHigherSFormation.nativeHigherSOut ActualHigherSFormation.nativeHigherSHalf
    simp only [map_add,inner_add_right,mul_add]
  have hRpt (x : R3) : μ x * ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ =
      R1 x+R2 x+R3f x := by
    dsimp only [R1,R2,R3f]
    unfold higherSAdjointOut higherSAdjointHalf
    simp only [map_add,inner_add_left,mul_add]
  have hLI : Integrable (fun x => μ x * ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ) :=
    ((hs.1.add ha.1).add hd.1).congr (Filter.Eventually.of_forall (fun x => (hLpt x).symm))
  have hRI : Integrable (fun x => μ x * ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ) :=
    ((hs.2.1.add ha.2.1).add hd.2.1).congr (Filter.Eventually.of_forall (fun x => (hRpt x).symm))
  have hLEq := (integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hLpt)).trans
    (integral_three_adds L1 L2 L3 hs.1 ha.1 hd.1)
  have hREq := (integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hRpt)).trans
    (integral_three_adds R1 R2 R3f hs.2.1 ha.2.1 hd.2.1)
  have hsum := congrArg₂ (fun a b : ℝ => a+b)
    (congrArg₂ (fun a b : ℝ => a+b) hs.2.2 ha.2.2) hd.2.2
  exact ⟨hLI,hRI,hLEq.trans (hsum.trans hREq.symm)⟩


theorem higherSAdjointOut_eq_zero_off_support (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ TS F0) :
    ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x = 0 :=
  (congrArg (fun v : Half => KL v)
    (higherSAdjointHalf_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x hx)).trans (map_zero KL)

theorem hasCompactSupport_higherSAdjointOut (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) :
    HasCompactSupport (ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0) :=
  ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _
    (higherSAdjointOut_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0)

/-- One-room higher-S contract: original forward formation plus the genuine
reverse formation and physical adjoint. No signed norm or coercivity premise. -/
def HigherSAdjointContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) : Prop :=
  ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
  ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
  ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ F0 : smoothCompactFiniteSphereCore hO hD,
    (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
    ActualHigherSFormation.HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0 ∧
    ContDiff ℝ ∞ (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) ∧
    ContDiff ℝ ∞ (ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0) ∧
    tsupport (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) ⊆ TS F0 ∧
    HasCompactSupport (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0) ∧
    HasCompactSupport (ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0) ∧
    ∀ G0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ) ∧
      (∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 G0 x⟫_ℝ) =
        ∫ x, referenceDensityFamily g L (q,x) *
          ⟪ADJO hreg δ0 W g2 δr Ar p hδr hAr q F0 x,G0.val x⟫_ℝ

theorem higherSAdjointContract_of_room (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) :
    HigherSAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ := by
  intro g2 hg2 δr Ar p hδr hAr q hq F0 hTF
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room g L y0 Φ B ε C ρ H a w hData
      hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F0 hTF
  · exact contDiff_higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF
  · exact contDiff_higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF
  · exact tsupport_higherSAdjointHalf_subset g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0
  · exact hasCompactSupport_higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0
  · exact hasCompactSupport_higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0
  · intro G0 hTG
    exact integrated_higherS_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG

/-- One retained W/radius BEFORE every second metric, profile and input, carrying
both original forward formation and the complete genuine higher-S reverse. -/
theorem exists_retained_higherS_adjoint (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ CRoom hreg δ0 W δ ∧
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      HigherSAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  exact ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,
    higherSAdjointContract_of_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointFormation
