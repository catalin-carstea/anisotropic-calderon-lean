import Calderon.ActualHigherSWholeScalarCommutator
import Calderon.ActualHigherSSumNegativeBounds
import Calderon.ActualDefectNorm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualScalarSAdjointCross
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ScalarBaseAdjoint ActualScalarPrincipalAdjoint PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorNativeForm ActualHigherSScalarCommutatorForm
  ActualHigherSFirstPhysicalCommutatorGraph ActualHigherSWholeScalarCommutator
  ActualHigherSZeroScalarCommutatorForm
section Generic
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma clm_coordinate_sum (T : R3 →L[ℝ] E) (X : R3) :
    T X = ∑ i : Fin 3, X i • T (coordinateDirection i) := by
  have he : (∑ i : Fin 3, X i • coordinateDirection i) = X := by
    ext j
    simp [coordinateDirection,Pi.single_apply]
  simpa only [map_sum,map_smul] using (congrArg T he).symm

lemma norm_clm_le_coordinate_sum (T : R3 →L[ℝ] E) :
    ‖T‖ ≤ ∑ i : Fin 3, ‖T (coordinateDirection i)‖ := by
  apply T.opNorm_le_bound (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro X
  rw [clm_coordinate_sum T X]
  calc
    _ ≤ ∑ i : Fin 3, ‖X i • T (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖X‖*‖T (coordinateDirection i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le X i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖T (coordinateDirection i)‖)*‖X‖ := by
      rw [← Finset.mul_sum,mul_comm]

lemma scalarSecondBase_linear_transfer (J : E →L[ℝ] V) (a : MatrixField)
    (u : R3 → E) (hu : ContDiff ℝ ∞ u) :
    (fun x => J (scalarSecondBase coordinateDirection a u x)) =
      scalarSecondBase coordinateDirection a (fun x => J (u x)) :=
  coordinateSecondAction_transfer J (fun i j x => a x i j) u hu

lemma scalarSecondBaseAdjoint_linear_transfer (J : E →L[ℝ] V) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) (hu : ContDiff ℝ ∞ u) :
    (fun x => J (scalarSecondBaseAdjoint coordinateDirection mu a u x)) =
      scalarSecondBaseAdjoint coordinateDirection mu a (fun x => J (u x)) := by
  funext x
  simp only [scalarSecondBaseAdjoint,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun y => (mu y*a y i j) • J (u y)) =
      fun y => J ((mu y*a y i j) • u y) := by funext y; rw [map_smul]
  rw [he]
  exact (directional_second_linear_input J (fun y => (mu y*a y i j) • u y)
    ((hm.mul (ha i j)).smul hu) (coordinateDirection j) (coordinateDirection i) x).symm

lemma contDiff_scalarSecondBaseAdjoint (mu : R3 → ℝ) (a : MatrixField) (u : R3 → E)
    (hmi : ContDiff ℝ ∞ (fun x => (mu x)⁻¹)) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (scalarSecondBaseAdjoint coordinateDirection mu a u) := by
  apply hmi.smul
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ _ ((hm.mul (ha i j)).smul hu))

lemma scalarSecondBaseAdjoint_eq_zero_off (mu : R3 → ℝ) (a : MatrixField) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (h0 : ∀ x ∉ K, u x = 0) (x : R3) (hx : x ∉ K) :
    scalarSecondBaseAdjoint coordinateDirection mu a u x = 0 := by
  have hD (i j : Fin 3) : ∀ y ∉ K,
      directionalFDeriv (coordinateDirection i) (fun z => (mu z*a z i j) • u z) y = 0 := by
    intro y hy
    exact directional_eq_zero_off _ K hK (fun z hz => by rw [h0 z hz,smul_zero]) _ y hy
  have hDD (i j : Fin 3) := directional_eq_zero_off _ K hK (hD i j) (coordinateDirection j) x hx
  simp only [scalarSecondBaseAdjoint,hDD,Finset.sum_const_zero,smul_zero]
end Generic
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
section Defect
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L q δr Ar : ℝ) (p : ℕ) (h : MatrixField)
local notation "mu" => (fun y => referenceDensityFamily g L (q,y))
local notation "aa" => actualPrincipalMatrix g L q δr Ar p h
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "v" => halfInput hO hD

def scalarDefectHalf (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  scalarSecondBaseAdjoint coordinateDirection mu aa (v F) x-
    scalarSecondBase coordinateDirection aa (v F) x

def scalarDefectPhysical (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  scalarSecondBaseAdjoint coordinateDirection mu aa F.val x-
    scalarSecondBase coordinateDirection aa F.val x

/-- Exact full physical graph of the scalar defect, with the original Sobolev inclusion. -/
theorem scalarDefectHalf_physical_graph (hg : IsAdmissibleMetric g)
    (hδr : 0 < δr) (hAr : 0 < Ar) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (scalarDefectHalf hO hD g L q δr Ar p h F x) =
      scalarDefectPhysical hO hD g L q δr Ar p h F x := by
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have ha := ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hv := contDiff_halfInput hO hD F
  have hd : (fun y => KL (v F y)) = F.val :=
    funext (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F)
  have hAdj := (congrFun (scalarSecondBaseAdjoint_linear_transfer KL mu aa (v F) hm ha hv) x).trans
    (congrArg (fun f : R3 → SphereL2 => scalarSecondBaseAdjoint coordinateDirection mu aa f x) hd)
  have hA := (congrFun (scalarSecondBase_linear_transfer KL aa (v F) hv) x).trans
    (congrArg (fun f : R3 → SphereL2 => scalarSecondBase coordinateDirection aa f x) hd)
  unfold scalarDefectHalf scalarDefectPhysical
  rw [map_sub]
  exact congrArg₂ (fun u z : SphereL2 => u-z) hAdj hA

lemma scalarDefectHalf_contDiff (hg : IsAdmissibleMetric g)
    (hδr : 0 < δr) (hAr : 0 < Ar) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (scalarDefectHalf hO hD g L q δr Ar p h F) := by
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x => (mu x)⁻¹) :=
    (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)
  have ha := ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hv := contDiff_halfInput hO hD F
  exact (contDiff_scalarSecondBaseAdjoint mu aa (v F) hmi hm ha hv).sub
    (contDiff_coordinateSecondAction (fun i j y => aa y i j) (v F) ha hv)

lemma scalarDefectHalf_eq_zero_off (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (hx : x ∉ tsupport F.val) : scalarDefectHalf hO hD g L q δr Ar p h F x = 0 := by
  have hz := halfInput_eq_zero_off hO hD F
  have hAdj := scalarSecondBaseAdjoint_eq_zero_off mu aa (v F) (tsupport F.val) (isClosed_tsupport F.val) hz x hx
  have hA := coordinateSecondAction_eq_zero_off (fun i j y => aa y i j) (v F)
    (tsupport F.val) (isClosed_tsupport F.val) hz x hx
  exact congrArg₂ (fun u z : Half => u-z) hAdj hA |>.trans (sub_self 0)
end Defect

section Numerical
private lemma weighted_cross_product (beta d m : ℝ) (hb : 1 ≤ beta) (hd : 0 ≤ d) (hm : 0 ≤ m) :
    (m+d/beta)*(d+m) ≤ 2*(beta⁻¹*d^2+beta*m^2) := by
  have hb0 : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hi : beta⁻¹ ≤ 1 := (inv_le_one₀ hb0).2 hb
  have hy : 2*d*m ≤ beta⁻¹*d^2+beta*m^2 := by
    calc
      _ ≤ (d^2+(beta*m)^2)/beta := (le_div_iff₀ hb0).2 (by nlinarith [sq_nonneg (d-beta*m)])
      _ = _ := by field_simp
  have h1 := mul_nonneg (sub_nonneg.mpr hi) (mul_nonneg hd hm)
  have h2 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg m)
  rw [div_eq_mul_inv]
  nlinarith

private lemma sum_three_norm_sq {E : Type*} [NormedAddCommGroup E] (v : Fin 3 → E) :
    (∑ i : Fin 3, ‖v i‖)^2 ≤ 3*∑ i : Fin 3, ‖v i‖^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),sq_nonneg (‖v 1‖-‖v 2‖)]
private lemma radius_le_one_of_small (r beta eps : ℝ) (hr : 0 ≤ r) (hb : 1 ≤ beta)
    (he : eps ≤ 1) (hs : r*beta^2 ≤ eps) : r ≤ 1 := by
  have h2 : 1 ≤ beta^2 := by nlinarith only [hb]
  have hn := mul_nonneg hr (sub_nonneg.mpr h2)
  nlinarith only [hs,he,hn]

private lemma defect_sum_product_numeric (r beta eps Cd Ks M I d m X Y f s : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hb : 1 ≤ beta) (he : 0 ≤ eps)
    (hCd : 0 ≤ Cd) (hKs : 0 ≤ Ks) (hM : 0 ≤ M) (hI : 0 ≤ I)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hf : 0 ≤ f)
    (hDef : X ≤ Cd*eps*(I*m+d/beta)) (hSum : Y ≤ Ks*(r^2*f+r*m))
    (hFrame : f ≤ 3*M*d) (hSq : d^2 ≤ 3*s) :
    X*Y ≤ (6*(Cd*(I+1))*((Ks+1)*(3*M+1)))*eps*(beta⁻¹*s+beta*m^2) := by
  have hb0 : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  let CD := Cd*(I+1)
  let CN := (Ks+1)*(3*M+1)
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hCN : 0 ≤ CN := by dsimp [CN]; positivity
  have hDef' : X ≤ CD*eps*(m+d/beta) := by
    apply hDef.trans
    dsimp only [CD]
    have hz1 := mul_nonneg (mul_nonneg (mul_nonneg hCd he) hI) (div_nonneg hd hb0.le)
    have hz2 := mul_nonneg (mul_nonneg hCd he) hm
    nlinarith only [hz1,hz2]
  have hr2 : r^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hE : r^2*f+r*m ≤ 3*M*d+m := by
    have h1 := mul_le_mul_of_nonneg_right hr2 hf
    have h2 := mul_le_mul_of_nonneg_right hr1 hm
    nlinarith only [h1,h2,hFrame]
  have hScale : Ks*(3*M*d+m) ≤ CN*(d+m) := by
    dsimp only [CN]
    nlinarith only [mul_nonneg hKs hd,mul_nonneg (mul_nonneg hKs hM) hm,
      mul_nonneg hM hd,mul_nonneg hM hm,hd,hm]
  have hSum' := hSum.trans ((mul_le_mul_of_nonneg_left hE hKs).trans hScale)
  have hNum := weighted_cross_product beta d m hb hd hm
  have hIE : beta⁻¹*d^2+beta*m^2 ≤ 3*(beta⁻¹*s+beta*m^2) := by
    have h1 := mul_le_mul_of_nonneg_left hSq (inv_nonneg.mpr hb0.le)
    have h2 := mul_nonneg hb0.le (sq_nonneg m)
    nlinarith only [h1,h2]
  calc
    _ ≤ (CD*eps*(m+d/beta))*(CN*(d+m)) := mul_le_mul hDef' hSum' hY (by positivity)
    _ = CD*CN*eps*((m+d/beta)*(d+m)) := by ring
    _ ≤ CD*CN*eps*(2*(beta⁻¹*d^2+beta*m^2)) := mul_le_mul_of_nonneg_left hNum (by positivity)
    _ ≤ CD*CN*eps*(2*(3*(beta⁻¹*s+beta*m^2))) := by gcongr
    _ = _ := by dsimp only [CD,CN]; ring

private lemma clm_frame_sum_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : R3 →L[ℝ] E) (e : Fin 3 → R3) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i, ‖e i‖ ≤ M) :
    (∑ i : Fin 3, ‖T (e i)‖) ≤ 3*M*(∑ j : Fin 3, ‖T (coordinateDirection j)‖) := by
  have hd := norm_clm_le_coordinate_sum T
  have hd0 : 0 ≤ ∑ j : Fin 3, ‖T (coordinateDirection j)‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg (T (coordinateDirection j)))
  calc
    _ ≤ ∑ _i : Fin 3, (∑ j : Fin 3, ‖T (coordinateDirection j)‖)*M := by
      apply Finset.sum_le_sum
      intro i _
      exact (T.le_opNorm (e i)).trans (mul_le_mul hd (he i) (norm_nonneg (e i)) hd0)
    _ = _ := by simp; ring

end Numerical

section FrameBound
variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
include hg
theorem exists_frame_norm_uniform_bound (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      ‖referenceMetricGramFrame g L (q,x) i‖ ≤ M := by
  obtain ⟨M,hM,hcap⟩ := exists_uniform_bound_finite_family
    (fun i z => ‖referenceMetricGramFrame g L z i‖)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.norm) K hK
  refine ⟨M,hM,?_⟩
  intro q hq x hx i
  simpa only [abs_of_nonneg (norm_nonneg _)] using hcap q hq x hx i
end FrameBound

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
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "BETA" => actualReferenceBeta g L
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "SH" => ActualHigherSFormation.nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

local notation "ADJ" => ActualHigherSAdjointFormation.higherSAdjointHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD
  g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "AO" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SN" => ActualHigherSFormation.nativeHigherSNegative hF hO hD
  g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "DH" => scalarDefectHalf hO hD g L
local notation "DP" => scalarDefectPhysical hO hD g L
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

attribute [local irreducible] ActualHigherSFormation.nativeHigherSNegative
  ActualHigherSAdjointFormation.higherSAdjointHalf sphereSobolevInclusionL

/-- Original-energy bound for the actual scalar defect paired with full S plus full S-adjoint. -/
theorem exists_actual_scalar_defect_S_sum_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
      ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      ∀ hh : (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)),
      ∀ F : smoothCompactFiniteSphereCore hO hD,
        (∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) →
        (∀ x ∈ tsupport F.val, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
          (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
        (∀ x ∈ tsupport F.val, ∀ᶠ y in 𝓝 x, (h y).IsHermitian) →
        (∀ x ∈ tsupport F.val, 1 ≤ BETA q δr Ar p x) →
        (∀ x ∈ tsupport F.val, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
        Integrable (fun x => referenceDensityFamily g L (q,x)*
          ⟪DP q δr Ar p h F x, SO δr Ar p hδr hAr q hreg δ0 W g2 F x+
            AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ) ∧
        Integrable (fun x => referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) ∧
        |∫ x, referenceDensityFamily g L (q,x)*
          ⟪DP q δr Ar p h F x, SO δr Ar p hδr hAr q hreg δ0 W g2 F x+
            AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ| ≤
          K*eps*∫ x, referenceDensityFamily g L (q,x)*
            finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x := by
  obtain ⟨Cd,hCd,hDcap⟩ := ActualDefectNorm.exists_actual_scalar_adjoint_defect_uniform_norm_bound
    (E := Half) g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Ks,hKs,hScap⟩ := ActualHigherSSumNegativeBounds.exists_actual_higherS_sum_negative_uniform_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
  obtain ⟨M,hM,hFrame⟩ := exists_frame_norm_uniform_bound g hg L (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cr,hCr,hEcap⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD
    g hg L (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  let CD := Cd*(‖IH‖+1)
  let CN := (Ks+1)*(3*M+1)
  have hCD : 0 < CD := mul_pos hCd (by positivity)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCN : 0 < CN := mul_pos (by linarith) (by positivity)
  refine ⟨6*CD*CN*Cr,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hsym hbeta hsmall
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := BETA q δr Ar p
  let u := UF F
  let v := halfInput hO hD F
  let nz : R3 → Neg := fun x => SN g2 q (referenceRadius δr Ar p L) u x+
    JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F x)
  let Vsum : R3 → Half := fun x => SH δr Ar p hδr hAr q hreg δ0 W g2 F x+
    ADJ hreg δ0 W g2 δr Ar p hδr hAr q F x
  have hsub : tsupport F.val ⊆ closedBall y0 ρ := by
    intro x hx
    simpa only [ActualHigherSFormation.higherSParam] using (hTF x hx).1.2.1
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have hbcont := continuous_actualReferenceBeta g hg L q δr Ar p hL hδr hAr
  have hbpos := actualReferenceBeta_pos g hg L q δr Ar p hL hδr hAr hp
  have hSO := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac
    g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hAO := ActualHigherSAdjointFormation.contDiff_higherSAdjointHalf
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F hTF
  have hVS : ContDiff ℝ ∞ Vsum := hSO.2.2.1.add hAO
  have hDH := scalarDefectHalf_contDiff hO hD g L q δr Ar p h hg hδr hAr hh F
  have hDH0 := scalarDefectHalf_eq_zero_off hO hD g L q δr Ar p h F
  have hSupp : Function.support (DH q δr Ar p h F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hx'
    exact hx (hDH0 x hx')
  have hcDH : HasCompactSupport (DH q δr Ar p h F) := F.property.2.1.mono' hSupp
  have hPairI : Integrable (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ) (DH q δr Ar p h F x) (nz x)) := by
    have he : (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ) (DH q δr Ar p h F x) (nz x)) =
        fun x => ⟪mu x • KL (Vsum x),KL (DH q δr Ar p h F x)⟫_ℝ := by
      funext x
      have hGraph : JL (Vsum x) = nz x :=
        (map_add JL _ _).trans (congrArg (fun z : Neg => z+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F x)) (hSO.2.2.2.1 x))
      rw [← hGraph,ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD]
      rw [real_inner_smul_left,real_inner_comm]
    rw [he]
    exact BaseDensityAdjoint.compact_inner_integrable _ _
      (hm.smul (((KL).contDiff.comp hVS))).continuous ((KL).contDiff.comp hDH).continuous
      (hcDH.comp_left (map_zero KL))
  have hPairEq : (fun x => mu x*sphereSobolevDualPairing (1/2 : ℝ) (DH q δr Ar p h F x) (nz x)) =
      fun x => mu x*⟪DP q δr Ar p h F x,SO δr Ar p hδr hAr q hreg δ0 W g2 F x+
        AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ := by
    funext x
    have hGraph : JL (Vsum x) = nz x :=
      (map_add JL _ _).trans (congrArg (fun z : Neg => z+JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F x)) (hSO.2.2.2.1 x))
    rw [← hGraph,ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD,
      scalarDefectHalf_physical_graph hO hD g L q δr Ar p h hg hδr hAr hh F x]
    simp only [Vsum,map_add,ActualHigherSFormation.nativeHigherSOut,ActualHigherSAdjointFormation.higherSAdjointOut]
  have hN := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbcont hbpos F
  have hPt : ∀ x, |mu x*sphereSobolevDualPairing (1/2 : ℝ) (DH q δr Ar p h F x) (nz x)| ≤
      (6*CD*CN*Cr)*eps*(mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) := by
    intro x
    by_cases hx : x ∈ tsupport F.val
    · let d := ∑ i : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection i))‖
      let m := ‖u x‖
      have hd0 : 0 ≤ d := Finset.sum_nonneg (fun i _ => norm_nonneg (IH (fderiv ℝ u x (coordinateDirection i))))
      have hm0 : 0 ≤ m := norm_nonneg (u x)
      have hvx : ‖v x‖ ≤ ‖IH‖*m := (IH).le_opNorm (u x)
      have he : ∀ X : R3, fderiv ℝ v x X = IH (fderiv ℝ u x X) := fun X =>
        directional_halfInput hO hD F X x
      have hDv : ‖fderiv ℝ v x‖ ≤ d := by simpa only [he] using norm_clm_le_coordinate_sum (fderiv ℝ v x)
      have hb1 := hbeta x hx
      have hb0 : 0 < beta x := lt_of_lt_of_le zero_lt_one hb1
      have hDef0 := hDcap q hq δr hδr hδr1 Ar hAr p hp x (hsub hx) eps heps heps1 h hh
        (hjet x hx) (hsym x hx) hb1 (hsmall x hx) v (contDiff_halfInput hO hD F)
      have hDef : ‖DH q δr Ar p h F x‖ ≤ Cd*eps*(‖IH‖*m+d/(beta x)) := hDef0.trans
        (mul_le_mul_of_nonneg_left (add_le_add hvx ((div_le_div_iff_of_pos_right hb0).2 hDv)) (by positivity))
      have hFrameD : (∑ i : Fin 3, ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖) ≤ 3*M*d := by
        simpa only [he] using clm_frame_sum_bound (fderiv ℝ v x)
          (fun i => referenceMetricGramFrame g L (q,x) i) M hM0 (hFrame q hq x (hsub hx))
      have hr0 : 0 ≤ referenceRadius δr Ar p L x := (referenceRadius_pos δr Ar p L x hδr hAr).le
      have hr1 := radius_le_one_of_small _ (beta x) eps hr0 hb1 heps1 (hsmall x hx)
      have hS : ‖nz x‖ ≤ Ks*((referenceRadius δr Ar p L x)^2*
          (∑ i : Fin 3, ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖)+
          referenceRadius δr Ar p L x*m) :=
        hScap δr Ar p hδr hδr1 hAr hp q hq F hTF hbeta (fun z hz => (hsmall z hz).trans heps1) x
      have hdsq := sum_three_norm_sq (E := Half) (fun i : Fin 3 => IH (fderiv ℝ u x (coordinateDirection i)))
      have hProd0 := defect_sum_product_numeric (referenceRadius δr Ar p L x) (beta x) eps Cd Ks M ‖IH‖ d m
        ‖DH q δr Ar p h F x‖ ‖nz x‖
        (∑ i : Fin 3, ‖IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))‖)
        (∑ i : Fin 3, ‖IH (fderiv ℝ u x (coordinateDirection i))‖^2)
        hr0 hr1 hb1 heps hCd.le hKs hM0 (norm_nonneg IH) hd0 hm0
        (norm_nonneg (DH q δr Ar p h F x)) (norm_nonneg (nz x))
        (Finset.sum_nonneg (fun i _ => norm_nonneg (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)))))
        hDef hS hFrameD hdsq
      have hProd : ‖DH q δr Ar p h F x‖*‖nz x‖ ≤ (6*CD*CN)*eps*inclusionEnergyDensity IH (beta x) u x := hProd0
      have hSource := native_threeHalf_angular_energy_le_finiteCoreSourceEnergy hO hD (beta x) F x
      have hEnergy := hSource.trans (hEcap q hq x (hsub hx) (beta x) hb1 F)
      have hFinal := hProd.trans (mul_le_mul_of_nonneg_left hEnergy (by positivity))
      rw [abs_mul,abs_of_nonneg (hmu x)]
      exact (mul_le_mul_of_nonneg_left (abs_sphereSobolevDualPairing_le (1/2 : ℝ) _ _) (hmu x)).trans
        ((mul_le_mul_of_nonneg_left hFinal (hmu x)).trans_eq (by ring))
    · rw [hDH0 x hx]
      simp only [halfPairing_zero_left,mul_zero,abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (hmu x)
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F x))
  refine ⟨hPairEq ▸ hPairI,hN,?_⟩
  rw [← hPairEq]
  calc
    _ ≤ ∫ x, |mu x*sphereSobolevDualPairing (1/2 : ℝ) (DH q δr Ar p h F x) (nz x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (6*CD*CN*Cr)*eps*(mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x) :=
      integral_mono hPairI.abs (hN.const_mul _) hPt
    _ = _ := by rw [integral_const_mul]


section InnerAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma scalar_cross_value (a ad s sd : E) :
    ⟪a,s⟫_ℝ-⟪ad,sd⟫_ℝ = -(⟪sd,a⟫_ℝ-⟪ad,s⟫_ℝ)-⟪ad-a,s+sd⟫_ℝ := by
  simp only [inner_sub_left,inner_add_right]
  rw [real_inner_comm sd a]
  ring

private lemma weighted_inner_compact_left (mu : R3 → ℝ) (u v : R3 → E)
    (hm : Continuous mu) (hu : Continuous u) (hv : Continuous v) (hc : HasCompactSupport u) :
    Integrable (fun x => mu x*⟪u x,v x⟫_ℝ) := by
  have hh := BaseDensityAdjoint.compact_inner_integrable (fun x => mu x • v x) u
    (hm.smul hv) hu hc
  have he : (fun x => ⟪mu x • v x,u x⟫_ℝ) = (fun x => mu x*⟪u x,v x⟫_ℝ) := by
    funext x
    rw [real_inner_smul_left,real_inner_comm]
  exact he ▸ hh

private lemma weighted_inner_compact_right (mu : R3 → ℝ) (u v : R3 → E)
    (hm : Continuous mu) (hu : Continuous u) (hv : Continuous v) (hc : HasCompactSupport v) :
    Integrable (fun x => mu x*⟪u x,v x⟫_ℝ) := by
  simpa only [real_inner_comm] using weighted_inner_compact_left mu v u hm hv hu hc
end InnerAlgebra

local notation "WO" => nativeWholeScalarCommutatorOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact scalar/S signed cross identity with all fields physical and unrestricted in angular output. -/
theorem actual_scalar_S_signed_cross_identity
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
    let A : R3 → SphereL2 := scalarSecondBase coordinateDirection (actualPrincipalMatrix g L q δr Ar p h) F.val
    let Ad : R3 → SphereL2 := scalarSecondBaseAdjoint coordinateDirection mu
      (actualPrincipalMatrix g L q δr Ar p h) F.val
    let Sf := SO δr Ar p hδr hAr q hreg δ0 W g2 F
    let Sd := AO hreg δ0 W g2 δr Ar p hδr hAr q F
    Integrable (fun x => mu x*(⟪A x,Sf x⟫_ℝ-⟪Ad x,Sd x⟫_ℝ)) ∧
    Integrable (fun x => mu x*⟪DP q δr Ar p h F x,Sf x+Sd x⟫_ℝ) ∧
    Integrable (fun x => mu x*⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ) ∧
    (∫ x, mu x*(⟪A x,Sf x⟫_ℝ-⟪Ad x,Sd x⟫_ℝ)) =
      -(∫ x, mu x*⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ)-
      ∫ x, mu x*⟪DP q δr Ar p h F x,Sf x+Sd x⟫_ℝ := by
  dsimp only
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let aa := actualPrincipalMatrix g L q δr Ar p h
  have ha := ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  let FA := coreCoordinateSecondAction hO hD (fun i j x => aa x i j) ha F
  let Af : R3 → SphereL2 := scalarSecondBase coordinateDirection aa F.val
  let Adf : R3 → SphereL2 := scalarSecondBaseAdjoint coordinateDirection mu aa F.val
  let Sf := SO δr Ar p hδr hAr q hreg δ0 W g2 F
  let Sd := AO hreg δ0 W g2 δr Ar p hδr hAr q F
  let SA := SO δr Ar p hδr hAr q hreg δ0 W g2 FA
  let AS := scalarSecondBase coordinateDirection aa Sf
  let Cf := WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x => (mu x)⁻¹) :=
    (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ x, 0 < mu x := fun x => referenceDensityFamily_pos g hg L (q,x)
  have hFA : FA.val = Af := funext (coreCoordinateSecondAction_apply hO hD (fun i j x => aa x i j) ha F)
  have hsub := coreCoordinateSecondAction_tsupport hO hD (fun i j x => aa x i j) ha F
  have hTA : ∀ x ∈ tsupport FA.val, (Tq δr Ar p q) x ∈ ParamRoom δ := fun x hx => hTF x (hsub hx)
  have hS := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq F hTF
  have hSf : ContDiff ℝ ∞ Sf := hS.2.2.2.2.2.1.1
  have hcSf : HasCompactSupport Sf := hS.2.2.2.2.2.1.2.2
  have hSd := ActualHigherSAdjointFormation.contDiff_higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F hTF
  have hcSd := ActualHigherSAdjointFormation.hasCompactSupport_higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W g2 δr Ar p hδr hAr q F
  have hAf : ContDiff ℝ ∞ Af := hFA ▸ FA.property.1
  have hcAf : HasCompactSupport Af := hFA ▸ FA.property.2.1
  have hAd : ContDiff ℝ ∞ Adf := contDiff_scalarSecondBaseAdjoint mu aa F.val hmi hm ha F.property.1
  have hAS : ContDiff ℝ ∞ AS := contDiff_coordinateSecondAction (fun i j x => aa x i j) Sf ha hSf
  have hTransfer := coordinateSecondAction_transfer KL (fun i j x => aa x i j)
    (SH δr Ar p hδr hAr q hreg δ0 W g2 F) hS.2.2.1
  have hCf : Cf = fun x => SA x-AS x := by
    funext x
    have hraw : Cf x = KL (SH δr Ar p hδr hAr q hreg δ0 W g2 FA x-
        coordinateSecondAction (fun i j y => aa y i j) (SH δr Ar p hδr hAr q hreg δ0 W g2 F) x) := rfl
    exact hraw.trans ((map_sub KL _ _).trans (congrArg
      (fun z : SphereL2 => KL (SH δr Ar p hδr hAr q hreg δ0 W g2 FA x)-z) (congrFun hTransfer x)))
  have hSadj := ActualHigherSAdjointFormation.integrated_higherS_physical_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F FA hTF hTA
  have hSadjEq : (∫ x, mu x*⟪F.val x,SA x⟫_ℝ) = ∫ x, mu x*⟪Sd x,Af x⟫_ℝ := by
    simpa only [hFA] using hSadj.2.2
  have hScalar := compact_scalarSecondBase_adjoint coordinateDirection mu aa Sf F.val
    hm ha hSf F.property.1 hcSf hp
  have hScalarEq : (∫ x, mu x*⟪F.val x,AS x⟫_ℝ) = ∫ x, mu x*⟪Adf x,Sf x⟫_ℝ := by
    calc
      _ = ∫ x, mu x*⟪AS x,F.val x⟫_ℝ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by rw [real_inner_comm]))
      _ = ∫ x, mu x*⟪Sf x,Adf x⟫_ℝ := hScalar
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by rw [real_inner_comm]))
  have hASi := weighted_inner_compact_left mu F.val AS hm.continuous F.property.1.continuous hAS.continuous F.property.2.1
  have hP1 := weighted_inner_compact_right mu Sd Af hm.continuous hSd.continuous hAf.continuous hcAf
  have hP2 := weighted_inner_compact_right mu Adf Sf hm.continuous hAd.continuous hSf.continuous hcSf
  have hWCfun : (fun x => mu x*⟪F.val x,Cf x⟫_ℝ) =
      fun x => mu x*⟪F.val x,SA x⟫_ℝ-mu x*⟪F.val x,AS x⟫_ℝ := by
    funext x
    rw [congrFun hCf x,inner_sub_right,mul_sub]
  have hWCi : Integrable (fun x => mu x*⟪F.val x,Cf x⟫_ℝ) := hWCfun.symm ▸ (hSadj.1.sub hASi)
  have hWCint : (∫ x, mu x*⟪F.val x,Cf x⟫_ℝ) =
      (∫ x, mu x*⟪Sd x,Af x⟫_ℝ)-(∫ x, mu x*⟪Adf x,Sf x⟫_ℝ) := by
    rw [hWCfun,integral_sub hSadj.1 hASi,hSadjEq,hScalarEq]
  have hC1 := weighted_inner_compact_right mu Af Sf hm.continuous hAf.continuous hSf.continuous hcSf
  have hC2 := weighted_inner_compact_right mu Adf Sd hm.continuous hAd.continuous hSd.continuous hcSd
  have hCi : Integrable (fun x => mu x*(⟪Af x,Sf x⟫_ℝ-⟪Adf x,Sd x⟫_ℝ)) := by
    have he : ((fun x => mu x*⟪Af x,Sf x⟫_ℝ)-(fun x => mu x*⟪Adf x,Sd x⟫_ℝ)) =
        (fun x => mu x*(⟪Af x,Sf x⟫_ℝ-⟪Adf x,Sd x⟫_ℝ)) := by funext x; exact (mul_sub _ _ _).symm
    exact he ▸ hC1.sub hC2
  have hDP : ContDiff ℝ ∞ (DP q δr Ar p h F) := hAd.sub hAf
  have hDi := weighted_inner_compact_right mu (DP q δr Ar p h F) (fun x => Sf x+Sd x)
    hm.continuous hDP.continuous (hSf.add hSd).continuous (hcSf.add hcSd)
  have hPoint : (fun x => mu x*(⟪Af x,Sf x⟫_ℝ-⟪Adf x,Sd x⟫_ℝ)) =
      fun x => -(mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ)-
        mu x*⟪DP q δr Ar p h F x,Sf x+Sd x⟫_ℝ := by
    funext x
    have ht := scalar_cross_value (Af x) (Adf x) (Sf x) (Sd x)
    change mu x*(⟪Af x,Sf x⟫_ℝ-⟪Adf x,Sd x⟫_ℝ) =
      -(mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ)-mu x*⟪Adf x-Af x,Sf x+Sd x⟫_ℝ
    rw [ht]
    ring
  refine ⟨hCi,hDi,hWCi,?_⟩
  have hPi : Integrable (fun x => mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ) := by
    have he : ((fun x => mu x*⟪Sd x,Af x⟫_ℝ)-(fun x => mu x*⟪Adf x,Sf x⟫_ℝ)) =
        (fun x => mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ) := by funext x; rfl
    exact he ▸ hP1.sub hP2
  have hPneg : Integrable (fun x => -(mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ)) := by
    have he : (-(fun x => mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ)) =
        (fun x => -(mu x*⟪Sd x,Af x⟫_ℝ-mu x*⟪Adf x,Sf x⟫_ℝ)) := by funext x; rfl
    exact he ▸ hPi.neg
  rw [hPoint,integral_sub hPneg hDi,integral_neg,integral_sub hP1 hP2,← hWCint]

/-- Literal scalar/S part of the physical signed squared-norm cross form. -/
def nativeScalarSCrossDensity
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (h : MatrixField)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪scalarSecondBase coordinateDirection (actualPrincipalMatrix g L q δr Ar p h) F.val x,
    SO δr Ar p hδr hAr q hreg δ0 W g2 F x⟫_ℝ-
  ⟪scalarSecondBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (q,y))
      (actualPrincipalMatrix g L q δr Ar p h) F.val x,
    AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ
local notation "SCross" => nativeScalarSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def ActualScalarSCrossFormBound
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
    ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    ∀ _hh : (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)),
    ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ tsupport F.val, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ tsupport F.val, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ tsupport F.val, ∀ᶠ y in 𝓝 x, (h y).IsHermitian) →
      (∀ x ∈ tsupport F.val, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ tsupport F.val, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*SCross hreg δ0 W g2 δr Ar p hδr hAr q h F x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*SCross hreg δ0 W g2 δr Ar p hδr hAr q h F x| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x
local notation "CrossForm" => ActualScalarSCrossFormBound
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact scalar/S mixed error bounded in the original four-term energy before all profiles and inputs. -/
theorem exists_actual_scalar_S_signed_cross_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    CrossForm hreg δ0 W δ g2 := by
  obtain ⟨KC,hKC,hCom⟩ := exists_actual_whole_scalar_physical_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
  obtain ⟨KD,hKD,hDef⟩ := exists_actual_scalar_defect_S_sum_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2
  refine ⟨KC+KD,add_pos hKC hKD,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hsym hbeta hsmall
  have hc := hCom δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hbeta hsmall
  have hd := hDef δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F hTF hjet hsym hbeta hsmall
  have hi := actual_scalar_S_signed_cross_identity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 hg2 δr Ar p hδr hAr q hq h hh F hTF
  refine ⟨hi.1,hc.2.1,?_⟩
  calc
    _ = |-(∫ x, referenceDensityFamily g L (q,x)*
        ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ)-
        (∫ x, referenceDensityFamily g L (q,x)*⟪DP q δr Ar p h F x,
          SO δr Ar p hδr hAr q hreg δ0 W g2 F x+AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ)| :=
      congrArg abs hi.2.2.2
    _ ≤ |∫ x, referenceDensityFamily g L (q,x)*
        ⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ|+
        |∫ x, referenceDensityFamily g L (q,x)*⟪DP q δr Ar p h F x,
          SO δr Ar p hδr hAr q hreg δ0 W g2 F x+AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        (-(∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,WO hreg δ0 W g2 δr Ar p hδr hAr q h hh F x⟫_ℝ))
        (-(∫ x, referenceDensityFamily g L (q,x)*⟪DP q δr Ar p h F x,
          SO δr Ar p hδr hAr q hreg δ0 W g2 F x+AO hreg δ0 W g2 δr Ar p hδr hAr q F x⟫_ℝ))
    _ ≤ KC*eps*(∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x)+
        KD*eps*(∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F x) :=
      add_le_add hc.2.2 hd.2.2
    _ = _ := by ring

/-- Same original W/room/Jacobian guard chosen before g2 and every shrinking profile. -/
theorem exists_retained_actual_scalar_S_signed_cross_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → CrossForm hreg δ0 W δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_S_signed_cross_reference_form g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hJac hL g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualScalarSAdjointCross
