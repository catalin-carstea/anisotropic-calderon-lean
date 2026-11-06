import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualAngularCoordinateTransposePairing
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAngularAdjoint
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEPairedGainedEndpoints NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualHorizontalNormBridge
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete



open SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicCore

/-- Exact high lift of the actual lowering output, from the physical degree graph.
The degree is k including the zero mode, and no finite-output assertion is made. -/
lemma inclusion_loweringInput_of_degree (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (u ub : Hi)
    (hub : IH ub = (sphereSobolevShiftedDegreeL (3/2 : ℝ) u : Half)) :
    IH (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
      (loweringHigh hF hO hD i ub)) = loweringHigh hF hO hD i u := by
  let a : Half := loweringHigh hF hO hD i u
  let b : Half := loweringHigh hF hO hD i ub
  have hc : loweringLow hF hO hD i
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) = JL b := by
    rw [← hub]
    exact (v017_inclusion_loweringHigh hF hO hD i ub).symm
  have hg := congrArg (fun T : Hi →L[ℝ] Neg => T u)
    (degreeLoweringHigh_graph hF hO hD i)
  have hd : JL (-a) =
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) a : Neg) - JL b := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg,
      ContinuousLinearMap.sub_apply, hc, a, b] using hg
  have hgraph : (sphereSobolevShiftedDegreeL (1/2 : ℝ) a : Neg) = JL (-a+b) :=
    ((sub_eq_iff_eq_add).mp hd.symm).trans ((map_add JL (-a) b).symm)
  have hl := inclusion_besselOrder_eq_of_half_degree_graph a (-a+b) hgraph
  have hcancel : (-a+b)+a = b := by abel
  rw [hcancel] at hl
  exact hl


/-- Explicit high lift of lowering applied to the original finite input. -/
def loweringInput (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (F0 : smoothCompactFiniteSphereCore hO hD)
    (i : Fin 3) (x : R3) : Hi :=
  sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
    (loweringHigh hF hO hD i (ActualHigherSFormation.higherSDegreeInput hO hD F0 x))

lemma loweringInput_inclusion (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (F0 : smoothCompactFiniteSphereCore hO hD)
    (i : Fin 3) (x : R3) :
    IH (loweringInput hF hO hD F0 i x) =
      loweringHigh hF hO hD i (ActualHigherSFormation.higherSInput hO hD F0 x) :=
  inclusion_loweringInput_of_degree hF hO hD i _ _
    (inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x)

lemma contDiff_loweringInput (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (F0 : smoothCompactFiniteSphereCore hO hD) (i : Fin 3) :
    ContDiff ℝ ∞ (loweringInput hF hO hD F0 i) :=
  (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)).contDiff.comp
    ((loweringHigh hF hO hD i).contDiff.comp
      (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0)))

lemma loweringInput_eq_zero_off_support (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (i : Fin 3) (z : R3)
    (hz : z ∉ tsupport (F0 : R3 → SphereL2)) : loweringInput hF hO hD F0 i z = 0 := by
  have hb := ActualReverseEHigherLift.revDegreeInput_eq_zero hO hD F0 z hz
  simp only [loweringInput,hb,map_zero]

lemma raising_pairing_lowering (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) (u v : Hi) :
    PP (IH u) (JL (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i v)) =
      PP (loweringHigh hF hO hD i u) (JL (IH v)) := by
  change PP (IH u) (JL (raisingHigh hF hO hD i v)) = _
  rw [v017_inclusion_raisingHigh hF hO hD i v]
  exact (v017_aA2 hF hO hD i u (IH v)).symm

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevDualPairing
  sphereSobolevHalfToSphereL2L loweringHigh raisingHigh sphereSobolevAngularCoordinateTransposeL

/-- Two exact angular rows, for arbitrary genuine E/e maps at one parameter point.
No symmetry of the coefficient matrix is used; the indices reverse exactly. -/
lemma angular_row_physical_adjoint (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (E e : Fin 3 → Hi →L[ℝ] Half)
    (hpivot : ∀ i u v, PP (E i u) (JL (IH v)) = PP (IH u) (JL (e i v)))
    (i j : Fin 3) (u v vf va ul vr : Hi)
    (hvf : IH vf = E j v)
    (hva : IH va = sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j v)
    (hul : IH ul = loweringHigh hF hO hD i u) (hvr : IH vr = e i u) :
    ⟪sphereSobolevHalfToSphereL2L hO hD (IH u),
      sphereSobolevHalfToSphereL2L hO hD
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i vf + E i va)⟫_ℝ =
    ⟪sphereSobolevHalfToSphereL2L hO hD (e j ul + loweringHigh hF hO hD j vr),
      sphereSobolevHalfToSphereL2L hO hD (IH v)⟫_ℝ := by
  let K := sphereSobolevHalfToSphereL2L hO hD
  have hP := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  have h1 : ⟪K (IH u), K (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i vf)⟫_ℝ =
      ⟪K (e j ul), K (IH v)⟫_ℝ := by
    calc
      _ = PP (IH u) (JL (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i vf)) := (hP _ _).symm
      _ = PP (loweringHigh hF hO hD i u) (JL (IH vf)) := raising_pairing_lowering hF hO hD i u vf
      _ = PP (IH ul) (JL (E j v)) := congrArg₂ (fun a b : Half => PP a (JL b)) hul.symm hvf
      _ = PP (E j v) (JL (IH ul)) := halfPairing_inclusion_symm _ _
      _ = PP (IH v) (JL (e j ul)) := hpivot j v ul
      _ = ⟪K (IH v), K (e j ul)⟫_ℝ := hP _ _
      _ = _ := real_inner_comm _ _
  have h2 : ⟪K (IH u), K (E i va)⟫_ℝ =
      ⟪K (loweringHigh hF hO hD j vr), K (IH v)⟫_ℝ := by
    calc
      _ = PP (IH u) (JL (E i va)) := (hP _ _).symm
      _ = PP (E i va) (JL (IH u)) := halfPairing_inclusion_symm _ _
      _ = PP (IH va) (JL (e i u)) := hpivot i va u
      _ = PP (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j v) (JL (IH vr)) := congrArg₂ (fun a b : Half => PP a (JL b)) hva hvr.symm
      _ = PP (IH vr) (JL (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j v)) := halfPairing_inclusion_symm _ _
      _ = PP (loweringHigh hF hO hD j vr) (JL (IH v)) := raising_pairing_lowering hF hO hD j vr v
      _ = _ := hP _ _
  simp only [map_add,inner_add_right,inner_add_left]
  exact congrArg₂ (fun a b : ℝ => a+b) h1 h2


private lemma inner_weighted_double_sum {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : H →L[ℝ] E) (c : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (u v : E) (f g : Fin 3 → Fin 3 → H)
    (h : ∀ i j, ⟪u,K (f i j)⟫_ℝ = ⟪K (g i j),v⟫_ℝ) :
    ⟪u,K (c • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • f i j)⟫_ℝ =
      ⟪K (c • ∑ i : Fin 3, ∑ j : Fin 3, Q i j • g i j),v⟫_ℝ := by
  simp only [map_smul,map_sum,inner_smul_right,real_inner_smul_left,inner_sum,sum_inner,h]

open MeasureTheory ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ConformalDepth
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UA" => ActualHigherSFormation.higherSRaisingInput hF hO hD
local notation "LA" => loweringInput hF hO hD
local notation "AH" => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
local notation "AL" => loweringHigh hF hO hD
local notation "FA" => ActualHigherSFormation.higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- Literal reverse of the actual angular S block: e_j a_i + a_j e_i,
with the SAME Q_ij and one retained W. -/
def revAngularHalf (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  referenceRadius δr Ar p L x • (∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      (eH j ((Tq δr Ar p q) x) (LA F0 i x) + AL j (VR hreg δ0 W δr Ar p q F0 i x)))
local notation "RA" => revAngularHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma raisingInput_inclusion (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (x : R3) :
    IH (UA F0 j x) = AH j (Uin F0 x) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreRaising hO hD hF j F0) x).trans
    (sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F0 x j).symm

lemma fwdAngular_eq_zero_off_support (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    FA δr Ar p q hreg δ0 W g2 F0 z = 0 := by
  have hv0 (j : Fin 3) := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j z hz
  have ha0 (j : Fin 3) := ActualHigherSFormation.higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0 j z hz
  simp only [ActualHigherSFormation.higherSAngularHalf,hv0,ha0,map_zero,add_zero,
    smul_zero,Finset.sum_const_zero]

lemma revAngular_eq_zero_off_support (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (z : R3) (hz : z ∉ TS F0) :
    RA hreg δ0 W g2 δr Ar p q F0 z = 0 := by
  have hr0 (i : Fin 3) := ActualReverseEHigherLift.reverseEHigherLift_eq_zero g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δr Ar p q F0 i z hz
  have hl0 (i : Fin 3) := loweringInput_eq_zero_off_support hF hO hD F0 i z hz
  simp only [revAngularHalf,hr0,hl0,map_zero,add_zero,smul_zero,Finset.sum_const_zero]

/-- Smooth forward angular block on the original membership-only common room. -/
theorem contDiff_fwdAngular (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (FA δr Ar p q hreg δ0 W g2 F0) := by
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hv (j : Fin 3) := ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hT j
  have hua (j : Fin 3) : ContDiff ℝ ∞ (UA F0 j) :=
    contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRaising hO hD hF j F0)
  have hua0 (j : Fin 3) := ActualHigherSFormation.higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q F0 j
  have he (i j : Fin 3) : ContDiff ℝ ∞ (fun x => EH i ((Tq δr Ar p q) x) (UA F0 j x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (EH i) F0
      (fun x hx => Cm.germHigh i _ (hT x hx)) (UA F0 j) (hua j) (hua0 j)
  have hQ := ActualCommonFirstWordQuadraticAdjoint.contDiff_frameCoefficient g L hg g2 hg2 q
  exact hRR.smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hQ i j).smul (((AH i).contDiff.comp (hv j)).add (he i j)))))

/-- Smooth genuine angular adjoint, no finite-output assertion. -/
theorem contDiff_revAngular (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (RA hreg δ0 W g2 δr Ar p q F0) := by
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hTs := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q
  have hvr (i : Fin 3) := ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hT i
  have hel (j i : Fin 3) : ContDiff ℝ ∞ (fun x => eH j ((Tq δr Ar p q) x) (LA F0 i x)) :=
    ActualReverseEHigherLift.reverseE_family_apply L hO hD δr Ar p q hTs (eH j) F0
      (fun x hx => Cm.rev.germHigh j _ (hT x hx)) (LA F0 i)
      (contDiff_loweringInput hF hO hD F0 i) (loweringInput_eq_zero_off_support hF hO hD F0 i)
  have hQ := ActualCommonFirstWordQuadraticAdjoint.contDiff_frameCoefficient g L hg g2 hg2 q
  exact hRR.smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (hQ i j).smul ((hel j i).add ((AL j).contDiff.comp (hvr i))))))

attribute [local irreducible] canonicalHigh reverseEHigh revAngularHalf
  ActualHigherSFormation.higherSLift ActualReverseEHigherLift.reverseEHigherLift
  ActualHigherSFormation.higherSAngularHalf loweringInput

/-- Exact global physical angular adjoint for independent test/input cores.
Every coefficient Q_ij and its original order is retained. -/
theorem pointwise_angular_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ =
      ⟪KL (RA hreg δ0 W g2 δr Ar p q F0 x),G0.val x⟫_ℝ := by
  by_cases hxF : x ∈ TS F0
  swap
  · have h0 : F0.val x = 0 := image_eq_zero_of_notMem_tsupport hxF
    simp only [h0,revAngular_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p q F0 x hxF,map_zero,inner_zero_left]
  by_cases hxG : x ∈ TS G0
  swap
  · have h0 : G0.val x = 0 := image_eq_zero_of_notMem_tsupport hxG
    simp only [h0,fwdAngular_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q G0 x hxG,map_zero,inner_zero_right]
  have ht := hTF x hxF
  have hFx : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  have hGx : G0.val x = KL (IH (Uin G0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD G0 x).symm
  have hrow (i j : Fin 3) :
      ⟪KL (IH (Uin F0 x)),KL (AH i (VF δr Ar p q hreg δ0 W G0 j x) + EH i ((Tq δr Ar p q) x) (UA G0 j x))⟫_ℝ =
      ⟪KL (eH j ((Tq δr Ar p q) x) (LA F0 i x) + AL j (VR hreg δ0 W δr Ar p q F0 i x)),KL (IH (Uin G0 x))⟫_ℝ :=
    angular_row_physical_adjoint hF hO hD (fun i => EH i ((Tq δr Ar p q) x))
      (fun i => eH i ((Tq δr Ar p q) x))
      (fun i u v => Cm.pivot i _ ht u v) i j (Uin F0 x) (Uin G0 x)
      (VF δr Ar p q hreg δ0 W G0 j x) (UA G0 j x) (LA F0 i x) (VR hreg δ0 W δr Ar p q F0 i x)
      (ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG j x)
      (raisingInput_inclusion hF hO hD G0 j x)
      (loweringInput_inclusion hF hO hD F0 i x)
      (ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm.rev δr Ar p q F0 hTF i x)
  have hs := inner_weighted_double_sum KL (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (KL (IH (Uin F0 x))) (KL (IH (Uin G0 x)))
    (fun i j => AH i (VF δr Ar p q hreg δ0 W G0 j x) + EH i ((Tq δr Ar p q) x) (UA G0 j x))
    (fun i j => eH j ((Tq δr Ar p q) x) (LA F0 i x) + AL j (VR hreg δ0 W δr Ar p q F0 i x)) hrow
  have hFwd : FA δr Ar p q hreg δ0 W g2 G0 x = referenceRadius δr Ar p L x •
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        (AH i (VF δr Ar p q hreg δ0 W G0 j x) + EH i ((Tq δr Ar p q) x) (UA G0 j x))) := by
    unfold ActualHigherSFormation.higherSAngularHalf
    rfl
  have hRev : RA hreg δ0 W g2 δr Ar p q F0 x = referenceRadius δr Ar p L x •
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        (eH j ((Tq δr Ar p q) x) (LA F0 i x) + AL j (VR hreg δ0 W δr Ar p q F0 i x))) := by
    unfold revAngularHalf
    rfl
  have hl := congrArg₂ (fun a : SphereL2 => fun b : Half => ⟪a,KL b⟫_ℝ) hFx hFwd
  have hr := congrArg₂ (fun a : Half => fun b : SphereL2 => ⟪KL a,b⟫_ℝ) hRev hGx
  exact hl.trans (hs.trans hr.symm)

/-- Integrated angular adjoint under the actual density, with both integrability claims. -/
theorem integrated_angular_physical_adjoint (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) * ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) * ⟪KL (RA hreg δ0 W g2 δr Ar p q F0 x),G0.val x⟫_ℝ) ∧
    (∫ x, referenceDensityFamily g L (q,x) * ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) * ⟪KL (RA hreg δ0 W g2 δr Ar p q F0 x),G0.val x⟫_ℝ := by
  have hpt := pointwise_angular_physical_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hc : Continuous (fun x => KL (FA δr Ar p q hreg δ0 W g2 G0 x)) :=
    (KL).continuous.comp (contDiff_fwdAngular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q G0 hTG).continuous
  have hcont := hmu.mul (F0.property.1.continuous.inner hc)
  have hcs : HasCompactSupport (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) :=
    ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx,inner_zero_left,mul_zero])
  have hI : Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine ⟨hI,?_,?_⟩
  · simpa only [hpt] using hI
  · simp only [hpt]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAngularAdjoint
