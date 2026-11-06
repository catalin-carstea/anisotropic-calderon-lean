import Calderon.ActualHigherSAdjointFormation
import Calderon.FixedParameterProfilePullback

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseELowInputDerivative
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualFiniteHarmonicCore ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualReverseEHigherLift ActualCommonFirstWordQuadraticAdjoint FixedParameterProfilePullback
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] lowNormed lowSpace

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
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "Uin" => higherSInput hO hD
local notation "VR" => reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TS" F:max => tsupport (F : R3 → SphereL2)

attribute [local irreducible] reverseEHigh reverseELow sphereSobolevInclusionL

/-- Global high/low compatibility on the actual input, from membership on its support only. -/
theorem reverseE_input_inclusion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ) (z : R3) (j : Fin 3) :
    JL (eH j ((Tq dr Ar p q) z) (Uin F z)) =
      eL j ((Tq dr Ar p q) z) (IH (Uin F z)) := by
  by_cases hz : z ∈ TS F
  · exact Cm.rev.compat j _ (hT z hz) _
  · have hU := revInput_eq_zero hO hD F z hz
    simp only [hU,map_zero]

/-- Exact derivative identity with only the included Half base derivative. -/
theorem reverseE_input_derivative (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F) (j : Fin 3) (X : R3) :
    JL (fderiv ℝ (fun z => eH j ((Tq dr Ar p q) z) (Uin F z)) x X) =
      eL j ((Tq dr Ar p q) x) (IH (fderiv ℝ (Uin F) x X)) +
        (fderiv ℝ (fun z => eL j ((Tq dr Ar p q) z)) x X) (IH (Uin F x)) := by
  let T := Tq dr Ar p q
  let U := Uin F
  let v : R3 → Half := fun z => eH j (T z) (U z)
  have hTs : ContDiff ℝ ∞ T :=
    contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr)
  have hTd : DifferentiableAt ℝ T x := hTs.differentiable (by simp) x
  have hUd : DifferentiableAt ℝ U x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F).differentiable (by simp) x
  have hAH : DifferentiableAt ℝ (fun z => eH j (T z)) x :=
    ((Cm.rev.germHigh j _ (hT x hx)).differentiableAt (by simp)).comp x hTd
  have hAL : DifferentiableAt ℝ (fun z => eL j (T z)) x :=
    ((Cm.rev.germLow j _ (hT x hx)).differentiableAt (by simp)).comp x hTd
  have hVd : DifferentiableAt ℝ v x := hAH.clm_apply hUd
  have hIUd : DifferentiableAt ℝ (fun z => IH (U z)) x :=
    (IH).differentiableAt.comp x hUd
  have hEq : (fun z => JL (v z)) = (fun z => eL j (T z) (IH (U z))) :=
    funext (fun z => reverseE_input_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm dr Ar p q F hT z j)
  have hMap : fderiv ℝ (fun z => JL (v z)) x X = JL (fderiv ℝ v x X) := by
    simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using
      congrArg (fun D : R3 →L[ℝ] Neg => D X) (((JL).hasFDerivAt.comp x hVd.hasFDerivAt).fderiv)
  have hInput : fderiv ℝ (fun z => IH (U z)) x X = IH (fderiv ℝ U x X) := by
    simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using
      congrArg (fun D : R3 →L[ℝ] Half => D X) (((IH).hasFDerivAt.comp x hUd.hasFDerivAt).fderiv)
  have hLow := congrArg (fun D : R3 →L[ℝ] Neg => D X) (fderiv_clm_apply hAL hIUd)
  have hLowEval : fderiv ℝ (fun z => eL j (T z) (IH (U z))) x X =
      eL j (T x) (fderiv ℝ (fun z => IH (U z)) x X) +
        (fderiv ℝ (fun z => eL j (T z)) x X) (IH (U x)) := by
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using hLow
  calc
    JL (fderiv ℝ v x X) = fderiv ℝ (fun z => JL (v z)) x X := hMap.symm
    _ = fderiv ℝ (fun z => eL j (T z) (IH (U z))) x X :=
      congrArg (fun f : R3 → Neg => fderiv ℝ f x X) hEq
    _ = eL j (T x) (fderiv ℝ (fun z => IH (U z)) x X) +
        (fderiv ℝ (fun z => eL j (T z)) x X) (IH (U x)) := hLowEval
    _ = eL j (T x) (IH (fderiv ℝ U x X)) +
        (fderiv ℝ (fun z => eL j (T z)) x X) (IH (U x)) :=
      congrArg (fun u : Half => eL j (T x) u +
        (fderiv ℝ (fun z => eL j (T z)) x X) (IH (U x))) hInput

/-- Whole original weighted horizontal reverse-lift word at negative order, with connection and degree. -/
theorem reverseE_weighted_horizontal_negative (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ TS F, (Tq dr Ar p q) z ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F) (i j : Fin 3) :
    JL (referenceHighWeightedHorizontalAction g L q (referenceRadius dr Ar p L)
      (VR hreg δ0 W dr Ar p q F j) x i) =
      (eL j ((Tq dr Ar p q) x) (IH (fderiv ℝ (Uin F) x (referenceMetricGramFrame g L (q,x) i))) +
        (fderiv ℝ (fun z => eL j ((Tq dr Ar p q) z)) x (referenceMetricGramFrame g L (q,x) i))
          (IH (Uin F x))) +
      referenceLowerHorizontalAngularL g L q x i (eH j ((Tq dr Ar p q) x) (Uin F x)) +
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (eH j ((Tq dr Ar p q) x) (Uin F x)) : Neg) := by
  let v : R3 → Half := fun z => eH j ((Tq dr Ar p q) z) (Uin F z)
  have hVR := contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm.rev dr Ar p hdr hAr q F hT j
  have hV : (fun z => IH (VR hreg δ0 W dr Ar p q F j z)) = v :=
    funext (fun z => reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm.rev dr Ar p q F hT j z)
  have hWeighted := referenceWeightedHorizontalAction_inclusion g L q (referenceRadius dr Ar p L)
    (VR hreg δ0 W dr Ar p q F j) x i (hVR.differentiable (by simp) x)
  have hReplace := congrArg
    (fun f : R3 → Half => referenceLowerWeightedHorizontalAction g L q (referenceRadius dr Ar p L) f x i) hV
  have hD := reverseE_input_derivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm dr Ar p hdr hAr q F hT x hx j (referenceMetricGramFrame g L (q,x) i)
  exact (hWeighted.trans hReplace).trans
    (congrArg (fun z : Neg =>
      z + referenceLowerHorizontalAngularL g L q x i (v x) +
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i •
          (sphereSobolevShiftedDegreeL (1/2 : ℝ) (v x) : Neg)) hD)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseELowInputDerivative
