import Calderon.ActualLowerUSFirstCoefficientJets
import Calderon.ActualLowerUSGainFirstCaps

/-!
GPT-6.1 Sol authoring support. The before-code derivative expansion is
lower-u-s-nov03-v001/second-row-next-upfront.md. This module assembles the
literal T product rule, keeping each actual coefficient and endpoint family.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualMixedAngularPairedGains ActualHigherSLeadingBracketGain ActualHigherSCoordinateWeightBounds
  FixedParameterProfilePullback FixedParameterProfileBudgets
  ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric

local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "LowMap" => Half →L[ℝ] Neg
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Scalar product derivative in an abstract canonical normed space. This
boundary is proved before introducing any concrete nested operator instances. -/
private theorem norm_fderiv_smul_le_generic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : R3 → ℝ) (A : R3 → E) (x : R3)
    (hb : DifferentiableAt ℝ b x) (hA : DifferentiableAt ℝ A x) :
    ‖fderiv ℝ (fun y => b y • A y) x‖ ≤
      |b x| * ‖fderiv ℝ A x‖ + ‖fderiv ℝ b x‖ * ‖A x‖ := by
  have hd : fderiv ℝ (fun y => b y • A y) x =
      b x • fderiv ℝ A x + (fderiv ℝ b x).smulRight (A x) := fderiv_fun_smul hb hA
  calc
    _ = ‖b x • fderiv ℝ A x + (fderiv ℝ b x).smulRight (A x)‖ := congrArg norm hd
    _ ≤ ‖b x • fderiv ℝ A x‖ + ‖(fderiv ℝ b x).smulRight (A x)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add
      (by simpa only [Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (b x) (fderiv ℝ A x))
      (le_of_eq (ContinuousLinearMap.norm_smulRight_apply (fderiv ℝ b x) (A x)))

/- Cache the canonical low-map structures only, following the qualified
physical Gain producer. No parameter-space structure or bare Norm override. -/
@[instance_reducible] private def secondRowDerivativeLowMapNormed : NormedAddCommGroup LowMap := inferInstance
attribute [local instance] secondRowDerivativeLowMapNormed
@[instance_reducible] private def secondRowDerivativeLowMapSpace : NormedSpace ℝ LowMap := inferInstance
attribute [local instance] secondRowDerivativeLowMapSpace

/-- A direct operator-norm estimate avoids any stronger exact norm-scalar
instance on the low-map space. -/
private theorem norm_low_smulRight_le (c : R3 →L[ℝ] ℝ) (A : LowMap) :
    ‖c.smulRight A‖ ≤ ‖c‖*‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg c) (norm_nonneg A))
  intro v
  change ‖c v • A‖ ≤ ‖c‖*‖A‖*‖v‖
  calc
    _ ≤ |c v| *‖A‖ := norm_smul_low_le (c v) A
    _ ≤ (‖c‖*‖v‖)*‖A‖ :=
      mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using c.le_opNorm v) (norm_nonneg A)
    _ = _ := by ring

private theorem norm_fderiv_low_smul_le (b : R3 → ℝ) (A : R3 → LowMap) (x : R3)
    (hb : DifferentiableAt ℝ b x) (hA : DifferentiableAt ℝ A x) :
    ‖fderiv ℝ (fun y => b y • A y) x‖ ≤
      |b x| *‖fderiv ℝ A x‖ + ‖fderiv ℝ b x‖*‖A x‖ :=
  norm_fderiv_smul_le_generic (E := LowMap) b A x hb hA

private theorem fderiv_finite_sum_at {ι : Type*} [Fintype ι]
    (A : ι → R3 → LowMap) (x : R3) (hA : ∀ i, DifferentiableAt ℝ (A i) x) :
    fderiv ℝ (fun y => ∑ i, A i y) x = ∑ i, fderiv ℝ (A i) x := by
  have hSum : HasFDerivAt (fun y => ∑ i, A i y)
      (∑ i, fderiv ℝ (A i) x) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hA i).hasFDerivAt)
  exact hSum.fderiv

private theorem norm_real_clm_le_three_coordinates (A : R3 →L[ℝ] ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hA : ∀ k : Fin 3, |A (coordinateDirection k)| ≤ M) : ‖A‖ ≤ 3*M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hu : (∑ k : Fin 3, u k • coordinateDirection k) = u := by
    ext k
    simp [coordinateDirection,WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,
      PiLp.single_apply,EuclideanSpace.single,Pi.single_apply]
  have he : A u = ∑ k : Fin 3, u k * A (coordinateDirection k) := by
    have hh := congrArg A hu
    simpa only [map_sum,map_smul,smul_eq_mul] using hh.symm
  have hcoord (k : Fin 3) : |u k| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u k
  calc
    ‖A u‖ = |∑ k : Fin 3, u k * A (coordinateDirection k)| := by rw [he]; rfl
    _ ≤ ∑ k : Fin 3, |u k * A (coordinateDirection k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, ‖u‖*M := Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hcoord k) (hA k) (abs_nonneg _) (norm_nonneg u))
    _ = (3*M)*‖u‖ := by simp only [Fin.sum_univ_three]; ring

private theorem norm_fderiv_real_mul_le (f h : R3 → ℝ) (x : R3)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    ‖fderiv ℝ (fun y => f y*h y) x‖ ≤
      |f x| *‖fderiv ℝ h x‖ + |h x| *‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hh]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [Real.norm_eq_abs] using
      ContinuousLinearMap.opNorm_smul_le (f x) (fderiv ℝ h x))
    (by simpa only [Real.norm_eq_abs] using
      ContinuousLinearMap.opNorm_smul_le (h x) (fderiv ℝ f x)))

/-- Scalar product arithmetic used only after its caps have been derived
from the original radius, coordinate-weight and H8 coefficient theorems. -/
private theorem scalar_factor_first_bound (r w c : R3 → ℝ) (x : R3)
    (hr : DifferentiableAt ℝ r x) (hw : DifferentiableAt ℝ w x) (hc : DifferentiableAt ℝ c x)
    (J MW CJ eta beta : ℝ) (hJ : 0 ≤ J) (hMW : 0 ≤ MW) (hCJ : 0 ≤ CJ)
    (heta : 0 ≤ eta) (hb : 1 ≤ beta) (hr0 : 0 ≤ r x) (hr1 : r x ≤ 1)
    (hR : ‖fderiv ℝ r x‖ ≤ J*beta) (hw0 : |w x| ≤ MW) (hw1 : ‖fderiv ℝ w x‖ ≤ MW)
    (hc0 : |c x| ≤ CJ*eta/beta) (hc1 : ‖fderiv ℝ c x‖ ≤ 3*CJ*eta) :
    |(r x)^2*w x*c x| ≤ ((2*J+5)*MW*CJ)*eta ∧
    ‖fderiv ℝ (fun y => (r y)^2*w y*c y) x‖ ≤ ((2*J+5)*MW*CJ)*eta := by
  have hbpos : 0 < beta := by linarith
  have hrate : 0 ≤ eta/beta := div_nonneg heta hbpos.le
  have hrate1 : eta/beta ≤ eta := (div_le_iff₀ hbpos).2 (by nlinarith)
  have hcancel : beta*(eta/beta) = eta := by field_simp [hbpos.ne']
  have hJb : 0 ≤ J*beta := mul_nonneg hJ hbpos.le
  have har : |r x| ≤ 1 := abs_le.mpr ⟨by linarith,hr1⟩
  have hr2 : |r x*r x| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg (r x)]
  have hr2smooth := hr.mul hr
  have hrr0 := norm_fderiv_real_mul_le r r x hr hr
  have hrrTerm : |r x| *‖fderiv ℝ r x‖ ≤ J*beta := by
    have hh := mul_le_mul har hR (norm_nonneg (fderiv ℝ r x)) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hrr : ‖fderiv ℝ (fun y => r y*r y) x‖ ≤ 2*J*beta := hrr0.trans (by linarith)
  have hrw0 : |(r x*r x)*w x| ≤ MW := by
    rw [abs_mul]
    exact (mul_le_mul hr2 hw0 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hrw1 : ‖fderiv ℝ (fun y => (r y*r y)*w y) x‖ ≤ MW+MW*(2*J*beta) := by
    apply (norm_fderiv_real_mul_le (fun y => r y*r y) w x hr2smooth hw).trans
    apply add_le_add
    · exact (mul_le_mul hr2 hw1 (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    · exact mul_le_mul hw0 hrr (norm_nonneg _) hMW
  have hcc : 0 ≤ CJ*eta/beta := div_nonneg (mul_nonneg hCJ heta) hbpos.le
  have hVal : |(r x*r x)*w x*c x| ≤ MW*CJ*eta := by
    rw [abs_mul]
    calc
      _ ≤ MW*(CJ*eta/beta) := mul_le_mul hrw0 hc0 (abs_nonneg _) hMW
      _ = (MW*CJ)*(eta/beta) := by ring
      _ ≤ (MW*CJ)*eta := mul_le_mul_of_nonneg_left hrate1 (mul_nonneg hMW hCJ)
      _ = _ := by ring
  have hD : ‖fderiv ℝ (fun y => (r y*r y)*w y*c y) x‖ ≤
      MW*(3*CJ*eta)+(CJ*eta/beta)*(MW+MW*(2*J*beta)) := by
    apply (norm_fderiv_real_mul_le (fun y => (r y*r y)*w y) c x (hr2smooth.mul hw) hc).trans
    exact add_le_add (mul_le_mul hrw0 hc1 (norm_nonneg _) hMW)
      (mul_le_mul hc0 hrw1 (norm_nonneg _) hcc)
  have hDScalar : MW*(3*CJ*eta)+(CJ*eta/beta)*(MW+MW*(2*J*beta)) ≤
      ((2*J+5)*MW*CJ)*eta := by
    calc
      _ = (MW*CJ)*(3*eta+eta/beta+2*J*(beta*(eta/beta))) := by ring
      _ = (MW*CJ)*(3*eta+eta/beta+2*J*eta) := by rw [hcancel]
      _ ≤ (MW*CJ)*(5*eta+2*J*eta) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hMW hCJ)
      _ = _ := by ring
  refine ⟨?_,?_⟩
  · have hh : MW*CJ*eta ≤ ((2*J+5)*MW*CJ)*eta := by
      have hbase : 1 ≤ 2*J+5 := by linarith
      have h := mul_le_mul_of_nonneg_right hbase (mul_nonneg (mul_nonneg hMW hCJ) heta)
      simpa only [one_mul,mul_assoc] using h
    simpa only [pow_two] using hVal.trans hh
  · simpa only [pow_two] using hD.trans hDScalar

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
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "Gain" => firstAngularGain
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "TC" => lowerUSSecondCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- The scalar factor of each literal T angular word, with the entire original
radius weight and the radius-independent actual S coordinate contraction. -/
def secondRowScalarFactor (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i j a : Fin 3) (v : FirstAngularIndex) (x : R3) : ℝ :=
  (referenceRadius dr Ar p L x)^2 * coordinateWeightBase g g2 L j a (q,x) *
    firstAngularCoefficient g L g2 q dr Ar p i x v

local notation "Scalar" => secondRowScalarFactor g L

/-- Exact finite product normal form of the genuine second-base row. -/
theorem lowerUSSecondCoefficient_eq_double_sum (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (i j : Fin 3) (x : R3) :
    TC mixed δ gen g2 q dr Ar p i j x =
      ∑ a : Fin 3, ∑ v : FirstAngularIndex, Scalar g2 q dr Ar p i j a v x •
        Gain mixed δ gen a ((Tq dr Ar p q) x) v := by
  simp only [lowerUSSecondCoefficient,firstGainCombination,secondRowScalarFactor,
    firstCoordinateWeight_eq_base,ActualHigherSFormation.higherSParam,Finset.smul_sum,smul_smul,mul_assoc]

include hg in
theorem contDiff_secondRowScalarFactor (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i j a : Fin 3) (v : FirstAngularIndex) :
    ContDiff ℝ ∞ (Scalar g2 q dr Ar p i j a v) :=
  (((ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr).pow 2).mul
    ((contDiff_coordinateWeightBase g g2 hg hg2 L j a).comp (contDiff_const.prodMk contDiff_id))).mul
      (contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i v)

/-- Exact local product rule. Every retained gain is the actual physical
pullback; finite sums refer only to the literal scalar/angular coefficient
inventory and do not truncate S or Sdag. -/
theorem lowerUSSecondCoefficient_fderiv_of_gain_smooth
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i j : Fin 3) (x : R3)
    (hGain : ∀ a : Fin 3, ∀ v : FirstAngularIndex,
      ContDiffAt ℝ ∞ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x) :
    ContDiffAt ℝ ∞ (TC mixed δ gen g2 q dr Ar p i j) x ∧
    fderiv ℝ (TC mixed δ gen g2 q dr Ar p i j) x =
      ∑ a : Fin 3, ∑ v : FirstAngularIndex,
        (Scalar g2 q dr Ar p i j a v x •
          fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x +
        (fderiv ℝ (Scalar g2 q dr Ar p i j a v) x).smulRight
          (Gain mixed δ gen a ((Tq dr Ar p q) x) v)) := by
  let A : Fin 3 → FirstAngularIndex → R3 → LowMap := fun a v y =>
    Scalar g2 q dr Ar p i j a v y • Gain mixed δ gen a ((Tq dr Ar p q) y) v
  have hA (a : Fin 3) (v : FirstAngularIndex) : ContDiffAt ℝ ∞ (A a v) x :=
    (contDiff_secondRowScalarFactor g L hg g2 hg2 q dr Ar p hdr hAr i j a v).contDiffAt.smul (hGain a v)
  have hEq : TC mixed δ gen g2 q dr Ar p i j = fun y => ∑ a : Fin 3, ∑ v : FirstAngularIndex, A a v y :=
    funext (fun y => lowerUSSecondCoefficient_eq_double_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen g2 q dr Ar p i j y)
  have hSum (a : Fin 3) : ContDiffAt ℝ ∞ (fun y => ∑ v : FirstAngularIndex, A a v y) x :=
    ContDiffAt.sum (fun v _ => hA a v)
  have hSmoothSum : ContDiffAt ℝ ∞ (fun y => ∑ a : Fin 3, ∑ v : FirstAngularIndex, A a v y) x :=
    ContDiffAt.sum (fun a _ => hSum a)
  have hOuter : fderiv ℝ (fun y => ∑ a : Fin 3, ∑ v : FirstAngularIndex, A a v y) x =
      ∑ a : Fin 3, fderiv ℝ (fun y => ∑ v : FirstAngularIndex, A a v y) x :=
    fderiv_finite_sum_at _ x (fun a => (hSum a).differentiableAt (by simp))
  have hInner (a : Fin 3) : fderiv ℝ (fun y => ∑ v : FirstAngularIndex, A a v y) x =
      ∑ v : FirstAngularIndex, fderiv ℝ (A a v) x :=
    fderiv_finite_sum_at _ x (fun v => (hA a v).differentiableAt (by simp))
  have hTerm (a : Fin 3) (v : FirstAngularIndex) : fderiv ℝ (A a v) x =
      Scalar g2 q dr Ar p i j a v x •
        fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x +
      (fderiv ℝ (Scalar g2 q dr Ar p i j a v) x).smulRight
        (Gain mixed δ gen a ((Tq dr Ar p q) x) v) :=
    fderiv_fun_smul
      ((contDiff_secondRowScalarFactor g L hg g2 hg2 q dr Ar p hdr hAr i j a v).differentiable (by simp) x)
      ((hGain a v).differentiableAt (by simp))
  have hCombined : (∑ a : Fin 3, fderiv ℝ (fun y => ∑ v : FirstAngularIndex, A a v y) x) =
      ∑ a : Fin 3, ∑ v : FirstAngularIndex,
        (Scalar g2 q dr Ar p i j a v x •
          fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x +
        (fderiv ℝ (Scalar g2 q dr Ar p i j a v) x).smulRight
          (Gain mixed δ gen a ((Tq dr Ar p q) x) v)) :=
    Finset.sum_congr rfl (fun a _ => (hInner a).trans (Finset.sum_congr rfl (fun v _ => hTerm a v)))
  have hTC : fderiv ℝ (TC mixed δ gen g2 q dr Ar p i j) x =
      fderiv ℝ (fun y => ∑ a : Fin 3, ∑ v : FirstAngularIndex, A a v y) x :=
    congrArg (fun f : R3 → LowMap => fderiv ℝ f x) hEq
  exact ⟨Eq.mpr (congrArg (fun f : R3 → LowMap => ContDiffAt ℝ ∞ f x) hEq) hSmoothSum,
    hTC.trans (hOuter.trans hCombined)⟩

/-- Actual-norm estimate of the complete derivative expansion. This is
bookkeeping, not an assumed quantitative error budget. -/
theorem lowerUSSecondCoefficient_fderiv_norm_le
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (i j : Fin 3) (x : R3)
    (hGain : ∀ a : Fin 3, ∀ v : FirstAngularIndex,
      ContDiffAt ℝ ∞ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x) :
    ‖fderiv ℝ (TC mixed δ gen g2 q dr Ar p i j) x‖ ≤
      ∑ a : Fin 3, ∑ v : FirstAngularIndex,
        (|Scalar g2 q dr Ar p i j a v x| *
          ‖fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x‖ +
        ‖fderiv ℝ (Scalar g2 q dr Ar p i j a v) x‖ *
          ‖Gain mixed δ gen a ((Tq dr Ar p q) x) v‖) := by
  have hD := (lowerUSSecondCoefficient_fderiv_of_gain_smooth
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 hg2 q dr Ar p hdr hAr i j x hGain).2
  have hNorm := congrArg (fun D : R3 →L[ℝ] LowMap => ‖D‖) hD
  apply hNorm.le.trans
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro a _ha
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro v _hv
  have hScalar := ContinuousLinearMap.opNorm_smul_le
    (Scalar g2 q dr Ar p i j a v x)
    (fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x)
  have hScalar' : ‖Scalar g2 q dr Ar p i j a v x •
      fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x‖ ≤
      |Scalar g2 q dr Ar p i j a v x| *
        ‖fderiv ℝ (fun y => Gain mixed δ gen a ((Tq dr Ar p q) y) v) x‖ := by
    simpa only [Real.norm_eq_abs] using hScalar
  have hRight := norm_low_smulRight_le (fderiv ℝ (Scalar g2 q dr Ar p i j a v) x)
    (Gain mixed δ gen a ((Tq dr Ar p q) x) v)
  exact (norm_add_le _ _).trans (add_le_add hScalar' hRight)

include hg in
/-- Fixed-g2 original-profile scalar factors and their actual first Fréchet
derivatives, with all constants chosen before the original profiles. -/
theorem exists_secondRowScalarFactor_uniform_first_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hL : 0 < L) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 ρ, 1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i j a : Fin 3, ∀ v : FirstAngularIndex,
      |Scalar g2 q dr Ar p i j a v x| ≤ CB*eta ∧
      ‖fderiv ℝ (Scalar g2 q dr Ar p i j a v) x‖ ≤ CB*eta := by
  obtain ⟨CJ,hCJ,hC⟩ := exists_firstAngularCoefficient_uniform_first_bounds
    g g2 hg hg2 L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨MW,hMW,hW⟩ := exists_coordinateWeightBase_uniform_first_caps g g2 hg hg2 L y0 ρ
  obtain ⟨J,hJ,hR⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _) 1
  refine ⟨(2*J+5)*MW*CJ,by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i j a v
  let r := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p x
  let ww : R3 → ℝ := fun y => coordinateWeightBase g g2 L j a (q,y)
  let cc : R3 → ℝ := fun y => firstAngularCoefficient g L g2 q dr Ar p i y v
  have hrpos : 0 < r x := referenceRadius_pos dr Ar p L x hdr hAr
  have hbpos : 0 < beta := by change 1 ≤ beta at hb; linarith
  have hb2 : 1 ≤ beta^2 := by change 1 ≤ beta at hb; nlinarith
  have hr1 : r x ≤ 1 := by
    have hh : r x ≤ r x*beta^2 := by nlinarith
    exact (hh.trans hs).trans heta1
  have hrc : ContDiff ℝ ∞ r := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hwc : ContDiff ℝ ∞ ww :=
    (contDiff_coordinateWeightBase g g2 hg hg2 L j a).comp (contDiff_const.prodMk contDiff_id)
  have hcc : ContDiff ℝ ∞ cc := contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i v
  have hr0 : ‖fderiv ℝ r x‖ ≤ J*(r x)*beta := by
    simpa only [norm_iteratedFDeriv_one,pow_one,r,beta,actualReferenceBeta] using
      (hR q hq dr hdr hdr1 Ar hAr p hp x hx).1
  have hrJ : ‖fderiv ℝ r x‖ ≤ J*beta := by
    calc
      _ ≤ J*(r x)*beta := hr0
      _ ≤ J*1*beta := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr1 hJ.le) hbpos.le
      _ = _ := by ring
  have hww0 : |ww x| ≤ MW := (hW q hq x hx j a).1
  have hww1 : ‖fderiv ℝ ww x‖ ≤ MW :=
    norm_fderiv_fixed_q_slice_le (coordinateWeightBase g g2 L j a)
      (contDiff_coordinateWeightBase g g2 hg hg2 L j a) q x MW (by linarith) (hW q hq x hx j a).2
  have hcc0 := hC q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i v
  have hcc1 : ‖fderiv ℝ cc x‖ ≤ 3*CJ*eta := by
    have hn := norm_real_clm_le_three_coordinates (fderiv ℝ cc x) (CJ*eta)
      (mul_nonneg hCJ.le heta) (fun k => hcc0.2 k)
    simpa only [mul_assoc] using hn
  exact scalar_factor_first_bound r ww cc x
    (hrc.differentiable (by simp) x) (hwc.differentiable (by simp) x) (hcc.differentiable (by simp) x)
    J MW CJ eta beta hJ.le (by linarith) hCJ.le heta hb hrpos.le hr1 hrJ hww0 hww1 hcc0.1 hcc1

/-- The actual T first derivative is uniformly O(eta) in the original profile.
This is fixed-g2; it proves no R/Z or full signed lower U/S estimate. -/
def LowerUSSecondCoefficientUniformDerivativeBound
    (mixed : MRoom) (δ : ℝ) (hδ : 0 < δ) (gen : GRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hL : 0 < L) : Prop :=
    ∃ CT : ℝ, 0 < CT ∧ ∃ etaT : ℝ,
      0 < etaT ∧ etaT ≤ data.eta0 ∧ etaT ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaT →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i j : Fin 3, ContDiffAt ℝ ∞ (TC mixed δ gen g2 q dr Ar p i j) x ∧
        ‖fderiv ℝ (TC mixed δ gen g2 q dr Ar p i j) x‖ ≤ CT*eta

theorem exists_lowerUSSecondCoefficient_uniform_derivative_bound
    (mixed : MRoom) (δ : ℝ) (hδ : 0 < δ) (gen : GRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hL : 0 < L) :
    LowerUSSecondCoefficientUniformDerivativeBound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ hδ gen g2 hg2 hL := by
  obtain ⟨CB,hCB,hB⟩ := exists_secondRowScalarFactor_uniform_first_bound g L y0 ρ hg g2 hg2 hL
  obtain ⟨M,hM,KT,hKT,etaT,hEtaT,hEtaT0,hEtaT1,hG⟩ :=
    exists_firstAngularGain_uniform_physical_first_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ hδ gen hL
  refine ⟨39*CB*M*(KT+1),by positivity,etaT,hEtaT,hEtaT0,hEtaT1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaT x hx hxBall hb hH8 hs i j
  have hgain := hG q hq dr hdr hdr1 Ar hAr p hp eta heta hetaT x hx hxBall hb hs
  have hscalar := hB q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaT.trans hEtaT1) x hx hb hH8 hs
  have hSmooth := fun a v => (hgain a v).1
  have hForm := lowerUSSecondCoefficient_fderiv_of_gain_smooth
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 hg2 q dr Ar p hdr hAr i j x hSmooth
  refine ⟨hForm.1,?_⟩
  apply (lowerUSSecondCoefficient_fderiv_norm_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 hg2 q dr Ar p hdr hAr i j x hSmooth).trans
  calc
    _ ≤ ∑ _a : Fin 3, ∑ _v : FirstAngularIndex, CB*M*(KT+1)*eta := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro v _hv
      have hh := add_le_add
        (mul_le_mul (hscalar i j a v).1 (hgain a v).2.2 (norm_nonneg _) (mul_nonneg hCB.le heta))
        (mul_le_mul (hscalar i j a v).2 (hgain a v).2.1 (norm_nonneg _) (mul_nonneg hCB.le heta))
      exact hh.trans_eq (by ring)
    _ = (39*CB*M*(KT+1))*eta := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,
        FirstAngularIndex,Generator,Fintype.card_sum,Fintype.card_prod,Fintype.card_unique]
      ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
