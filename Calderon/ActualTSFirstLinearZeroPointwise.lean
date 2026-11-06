import Calderon.ActualTFirstNegativeGraph
import Calderon.ActualTSLowerZeroZeroBinding
import Calderon.ActualTSZeroLiteralRegularity
import Calderon.ActualTSPrincipalLowerReferenceOrders

/-! Exact first-T / linear-zero-S component of original D10.
The original quadratic component is retained explicitly and is not estimated here.
Before-code: ../T-first-S-linear-zero-before-source-nov03-night-v001/. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroPointwise
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTFirstNegativeGraph ActualTFirstPhysicalDictionary ActualTSLowerZeroZeroBinding
  ActualSZeroPhysicalWordDictionary ActualHigherSScalarCommutatorForm
  ActualHigherSScalarCommutatorNativeForm ActualHigherSZeroScalarCommutatorForm PrincipalCommutator
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed negDualSpace
local notation "PN" => ‖PL‖+1

private lemma original_pair_bound (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Half) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖JL a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    |⟪sphereSobolevHalfToSphereL2L hO hD a,
      sphereSobolevHalfToSphereL2L hO hD b⟫_ℝ| ≤ PN*B*A := by
  have heq :
      ⟪sphereSobolevHalfToSphereL2L hO hD a,
        sphereSobolevHalfToSphereL2L hO hD b⟫_ℝ=PL b (JL a) :=
    (real_inner_comm _ _).trans
      (ActualHigherSZeroAtomTransport.half_pairing_inner hO hD b a).symm
  rw [heq]
  have hPN : 0 ≤ PN := by positivity
  have hNorm : |PL b (JL a)| ≤ ‖PL‖*‖b‖*‖JL a‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ PL b (JL a)
  have hP : ‖PL‖ ≤ PN := by linarith
  exact hNorm.trans (mul_le_mul (mul_le_mul hP hb (norm_nonneg _) hPN)
    ha (norm_nonneg _) (mul_nonneg hPN hB))

private lemma signed_equal_scalar_bound (a b K : ℝ) (ha : |a| ≤ K) (hb : |b| ≤ K) :
    |4*a-4*b| ≤ 8*K := by
  have h := (abs_sub (4*a) (4*b)).trans (add_le_add
    (by simpa only [abs_mul,show |(4 : ℝ)|=4 by norm_num] using
      mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤4))
    (by simpa only [abs_mul,show |(4 : ℝ)|=4 by norm_num] using
      mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)))
  exact h.trans_eq (by ring)

private lemma first_row_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t td z2 t2 z1 t1 s sd : E) (hs : s=z2+z1) (hsd : sd=t2+t1) :
    4*(⟪t,s⟫_ℝ-⟪td,sd⟫_ℝ) =
      (4*⟪t,z2⟫_ℝ-4*⟪td,t2⟫_ℝ)+(4*⟪t,z1⟫_ℝ-4*⟪td,t1⟫_ℝ) := by
  rw [hs,hsd]
  simp only [inner_add_right]
  ring

private lemma mass_sum_le (m e : ℝ) (d : Fin 3 → ℝ)
    (h : ∀ i, m*d i ≤ e) : m*(∑ i : Fin 3, d i) ≤ 3*e := by
  calc
    _ = ∑ i : Fin 3, m*d i := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin 3, e := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)

local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "TF" => referenceFirstHalf hO hD hF g L
local notation "TD" => referenceAdjointFirstHalf hO hD hF g L
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Exact signed factor-four first-T / linear-zero-S physical component. -/
def firstLinearZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*⟪KL (TF q (UF F) x),KL (Z1 g2 dr Ar p q x (UF F x))⟫_ℝ-
    4*⟪KL (TD q (UF F) x),KL (T1 g2 dr Ar p q x (UF F x))⟫_ℝ

/-- The exact remaining quadratic part, whose energy estimate is a separate obligation. -/
def firstQuadraticZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*⟪KL (TF q (UF F) x),KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
    4*⟪KL (TD q (UF F) x),KL (T2 g2 dr Ar p q F x)⟫_ℝ
local notation "LD" => firstLinearZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "QD" => firstQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "D10" => originalFirstZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] referenceFirstHalf referenceAdjointFirstHalf
  originalFirstNegative originalAdjointFirstNegative
  firstLinearZeroCrossDensity firstQuadraticZeroCrossDensity
  ActualHigherSFormation.higherSInput sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSLinearZero.linearZeroHigh ActualHigherSLinearZero.linearAdjointZeroHigh
  ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Actual pre-profile constant and threshold, preserving the original D10 split. -/
theorem exists_original_first_linear_zero_pointwise_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Clinear etaLinear : ℝ, 0 < Clinear ∧ 0 < etaLinear ∧ etaLinear ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaLinear →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ tsupport F.val,
        |LD g2 dr Ar p q F x| ≤ Clinear*eta*inclusionEnergyDensity IH
          (actualReferenceBeta g L q dr Ar p x) (UF F) x) ∧
      (∀ x, D10 g2 dr Ar p hdr hAr q F x=QD g2 dr Ar p q F x+LD g2 dr Ar p q F x) := by
  obtain ⟨CT,hCT,hFirst⟩ := exists_original_first_negative_uniform_bound hF hO hD g L hg y0 ρ
  obtain ⟨CL,hCL,hLinear⟩ := ActualHigherSLinearZero.exists_linear_zero_high_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨etaD,heD,heD0,hDict⟩ := exists_original_zero_physical_word_dictionary
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  let Clinear : ℝ := 24*PN*CL*CT
  have hPN : 0 < PN := by positivity
  have hClinear : 0 < Clinear := by dsimp only [Clinear]; positivity
  refine ⟨Clinear,min etaD 1,hClinear,lt_min heD zero_lt_one,
    (min_le_left _ _).trans heD0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have heDict : eta ≤ etaD := he.trans (min_le_left _ _)
  have he0 : eta ≤ data.eta0 := heDict.trans heD0
  have he1 : eta ≤ 1 := he.trans (min_le_right _ _)
  have hDct := hDict q hq dr hdr hdr1 Ar hAr p hp eta heta heDict K hK hKball F hsupp hb hs
  constructor
  · intro x hx
    have hxK := hsupp hx
    have hxBall := hKball hxK
    have hxClosed := ball_subset_closedBall hxBall
    let U := UF F
    let r := referenceRadius dr Ar p L x
    let beta := actualReferenceBeta g L q dr Ar p x
    let d : Fin 3 → ℝ := fun l => ‖IH (fderiv ℝ U x (coordinateDirection l))‖
    let m : ℝ := ‖U x‖
    let e : ℝ := inclusionEnergyDensity IH beta U x
    have hbX : 1 ≤ beta := hb x hxK
    have hb0 : 0 ≤ beta := zero_le_one.trans hbX
    have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
    have hd : 0 ≤ ∑ l : Fin 3, d l := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have heN : 0 ≤ e := inclusionEnergyDensity_nonneg IH beta U x hb0
    have hFirstX := hFirst q hq x hxClosed U
    have hTG : ‖JL (TF q U x)‖ ≤ CT*(∑ l : Fin 3, d l) :=
      (congrArg (fun z : Neg => ‖z‖) (original_first_negative_graph hF hO hD g L q U x)).le.trans hFirstX.1
    have hTDG : ‖JL (TD q U x)‖ ≤ CT*(∑ l : Fin 3, d l) :=
      (congrArg (fun z : Neg => ‖z‖) (original_adjoint_first_negative_graph hF hO hD g L q U x)).le.trans hFirstX.2
    have hLin := hLinear q hq dr hdr hdr1 Ar hAr p hp eta heta he0 x hxClosed hxBall hbX (hs x hxK)
    have hZ : ‖Z1 g2 dr Ar p q x (U x)‖ ≤ CL*r^2*beta*m :=
      ((Z1 g2 dr Ar p q x).le_opNorm (U x)).trans
        (mul_le_mul_of_nonneg_right hLin.1 (norm_nonneg _))
    have hT : ‖T1 g2 dr Ar p q x (U x)‖ ≤ CL*r^2*beta*m :=
      ((T1 g2 dr Ar p q x).le_opNorm (U x)).trans
        (mul_le_mul_of_nonneg_right hLin.2 (norm_nonneg _))
    have hForward := original_pair_bound hO hD (TF q U x) (Z1 g2 dr Ar p q x (U x))
      (CT*(∑ l : Fin 3, d l)) (CL*r^2*beta*m) (by positivity) (by positivity) hTG hZ
    have hReverse := original_pair_bound hO hD (TD q U x) (T1 g2 dr Ar p q x (U x))
      (CT*(∑ l : Fin 3, d l)) (CL*r^2*beta*m) (by positivity) (by positivity) hTDG hT
    have hSigned : |LD g2 dr Ar p q F x| ≤
        (8*PN*CL*CT)*(r^2*beta)*(m*(∑ l : Fin 3, d l)) := by
      have hBase := signed_equal_scalar_bound _ _ _ hForward hReverse
      have hDef : LD g2 dr Ar p q F x =
          4*⟪KL (TF q U x),KL (Z1 g2 dr Ar p q x (U x))⟫_ℝ-
          4*⟪KL (TD q U x),KL (T1 g2 dr Ar p q x (U x))⟫_ℝ := by
        unfold firstLinearZeroCrossDensity
        rfl
      rw [hDef]
      exact hBase.trans_eq (by ring)
    have hMixed : m*(∑ l : Fin 3, d l) ≤ 3*e := mass_sum_le m e d (fun l => by
      change ‖U x‖*‖IH (fderiv ℝ U x (coordinateDirection l))‖ ≤
        inclusionEnergyDensity IH beta U x
      calc
        _ = ‖IH (fderiv ℝ U x (coordinateDirection l))‖*‖U x‖ := mul_comm _ _
        _ ≤ _ := inclusion_energy_mixed_le IH beta U x (zero_lt_one.trans_le hbX) l)
    have hRsmall : r*beta^2 ≤ eta := hs x hxK
    have hr1 : r ≤ 1 := by
      calc
        r = r*1 := (mul_one r).symm
        _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hbX] : (1:ℝ)≤beta^2) hr
        _ ≤ eta := hRsmall
        _ ≤ 1 := he1
    have hSmall2 : r^2*beta^2 ≤ eta := by
      calc
        _ = r*(r*beta^2) := by ring
        _ ≤ 1*eta := mul_le_mul hr1 hRsmall (mul_nonneg hr (sq_nonneg _)) (by norm_num)
        _ = eta := one_mul _
    have hSmall : r^2*beta ≤ eta :=
      (mul_le_mul_of_nonneg_left (by nlinarith only [hbX] : beta≤beta^2) (sq_nonneg r)).trans hSmall2
    calc
      _ ≤ (8*PN*CL*CT)*(r^2*beta)*(m*(∑ l : Fin 3, d l)) := hSigned
      _ ≤ (8*PN*CL*CT)*(r^2*beta)*(3*e) :=
        mul_le_mul_of_nonneg_left hMixed (by positivity)
      _ = Clinear*(r^2*beta)*e := by dsimp only [Clinear]; ring
      _ ≤ Clinear*eta*e := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSmall hClinear.le) heN
  · intro x
    have hd := hDct x
    simpa only [originalFirstZeroCrossDensity,firstQuadraticZeroCrossDensity,firstLinearZeroCrossDensity] using
      first_row_split (KL (TF q (UF F) x)) (KL (TD q (UF F) x))
        (KL (Z2 g2 dr Ar p q F x)) (KL (T2 g2 dr Ar p q F x))
        (KL (Z1 g2 dr Ar p q x (UF F x))) (KL (T1 g2 dr Ar p q x (UF F x)))
        _ _ hd.1 hd.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroPointwise
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstLinearZeroPointwise.exists_original_first_linear_zero_pointwise_bound
