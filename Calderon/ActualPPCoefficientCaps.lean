import Calderon.ActualPPLowerRemainder
import Calderon.ActualHigherSLeadingWeightedJetBounds

/-! Author source after actual-pp-upfront-v001. UNCOMPILED.
Actual four first-coefficient caps, independently using retained high AND low
endpoint caps. No cap callback occurs in the final actual producer statement. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPCoefficientCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ActualHigherSLeadingWeightedJetBounds
  ActualHigherSCoordinateWeightBounds FixedParameterProfilePullback
  ConformalDepth PrincipalCommutator ActualPPLowerRemainder
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section Generic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Independent value/first physical derivative caps for a radius-squared,
three-row weighted family; every scalar/operator/radius derivative is kept. -/
theorem radius_squared_weighted_first_caps
    (R : R3 → ℝ) (a : Fin 3 → R3 → ℝ) (E : Fin 3 → R3 → V) (x : R3)
    (beta Ma B0 B1 J : ℝ) (hb : 1 ≤ beta) (hMa : 0 ≤ Ma)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hJ : 0 ≤ J) (hr0 : 0 ≤ R x)
    (hR : ContDiffAt ℝ ∞ R x)
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hE : ∀ i, ContDiffAt ℝ ∞ (E i) x)
    (ha0 : ∀ i, ‖a i x‖ ≤ Ma) (ha1 : ∀ i, ‖fderiv ℝ (a i) x‖ ≤ Ma)
    (hE0 : ∀ i, ‖E i x‖ ≤ B0) (hE1 : ∀ i, ‖fderiv ℝ (E i) x‖ ≤ B1)
    (hR1 : ‖fderiv ℝ R x‖ ≤ J*R x*beta) :
    ContDiffAt ℝ ∞ (fun y => (R y)^2 • (∑ i : Fin 3, a i y • E i y)) x ∧
    ‖(R x)^2 • (∑ i : Fin 3, a i x • E i x)‖ ≤ (3*Ma*B0)*(R x)^2 ∧
    ‖fderiv ℝ (fun y => (R y)^2 • (∑ i : Fin 3, a i y • E i y)) x‖ ≤
      (3*Ma*(2*J*B0+B0+B1))*(R x)^2*beta := by
  let S : R3 → V := fun y => ∑ i : Fin 3, a i y • E i y
  have hsmooth : ContDiffAt ℝ ∞ S x := ContDiffAt.sum (fun i _ => (ha i).smul (hE i))
  have hrow0 (i : Fin 3) : ‖a i x • E i x‖ ≤ Ma*B0 := by
    rw [norm_smul]
    exact mul_le_mul (ha0 i) (hE0 i) (norm_nonneg _) hMa
  have hrow1 (i : Fin 3) : ‖fderiv ℝ (fun y => a i y • E i y) x‖ ≤ Ma*B1+Ma*B0 := by
    have h := norm_fderiv_scalar_smul_le (a i) (E i) x
      ((ha i).differentiableAt (by simp)) ((hE i).differentiableAt (by simp))
    exact h.trans (add_le_add
      (mul_le_mul (ha0 i) (hE1 i) (norm_nonneg _) hMa)
      (mul_le_mul (ha1 i) (hE0 i) (norm_nonneg _) hMa))
  have hS0 : ‖S x‖ ≤ 3*Ma*B0 := by
    calc
      _ ≤ ∑ i : Fin 3, ‖a i x • E i x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, Ma*B0 := Finset.sum_le_sum (fun i _ => hrow0 i)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hDS : fderiv ℝ S x = ∑ i : Fin 3, fderiv ℝ (fun y => a i y • E i y) x := by
    have hSfun : S = ∑ i : Fin 3,(fun y => a i y • E i y) := by
      funext y
      simp only [S,Finset.sum_apply]
    rw [hSfun]
    exact fderiv_sum (fun i _ => ((ha i).differentiableAt (by simp)).smul
      ((hE i).differentiableAt (by simp)))
  have hS1 : ‖fderiv ℝ S x‖ ≤ 3*Ma*(B0+B1) := by
    rw [hDS]
    calc
      _ ≤ ∑ i : Fin 3, ‖fderiv ℝ (fun y => a i y • E i y) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, (Ma*B1+Ma*B0) := Finset.sum_le_sum (fun i _ => hrow1 i)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hR2 : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*R x*‖fderiv ℝ R x‖ := by
    have h := norm_fderiv_scalar_smul_le R R x
      (hR.differentiableAt (by simp)) (hR.differentiableAt (by simp))
    have hn : ‖R x‖=R x := by rw [Real.norm_eq_abs,abs_of_nonneg hr0]
    calc
      _ ≤ ‖R x‖*‖fderiv ℝ R x‖+‖fderiv ℝ R x‖*‖R x‖ := by
        simpa only [smul_eq_mul,pow_two] using h
      _ = _ := by rw [hn]; ring
  have hS10 : 0 ≤ 3*Ma*(B0+B1) := by positivity
  have hS1beta : 3*Ma*(B0+B1) ≤ (3*Ma*(B0+B1))*beta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hS10
  refine ⟨(hR.pow 2).smul hsmooth,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hS0 (sq_nonneg _)).trans (le_of_eq (by ring))
  · have h := norm_fderiv_scalar_smul_le (fun y => (R y)^2) S x
      ((hR.pow 2).differentiableAt (by simp)) (hsmooth.differentiableAt (by simp))
    have hR2' : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*R x*(J*R x*beta) :=
      hR2.trans (mul_le_mul_of_nonneg_left hR1 (by positivity))
    have hnR : ‖(R x)^2‖=(R x)^2 := by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖(R x)^2‖*‖fderiv ℝ S x‖+‖fderiv ℝ (fun y => (R y)^2) x‖*‖S x‖ := h
      _ ≤ (R x)^2*((3*Ma*(B0+B1))*beta)+(2*R x*(J*R x*beta))*(3*Ma*B0) := by
        rw [hnR]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hS1.trans hS1beta) (sq_nonneg _))
          (mul_le_mul hR2' hS0 (norm_nonneg _) (by positivity))
      _ = _ := by ring

/-- Uniform target shape for the actual independent four coefficient caps. -/
def FirstCaps (f : R3 → V) (R : R3 → ℝ) (beta : R3 → ℝ) (M : ℝ) (x : R3) : Prop :=
  ContDiffAt ℝ ∞ f x ∧ ‖f x‖ ≤ M*(R x)^2 ∧ ‖fderiv ℝ f x‖ ≤ M*(R x)^2*(beta x)

/-- Independent enlargement of the already proved three generic cap conclusions. -/
private lemma firstCaps_of_bounds (f : R3 → V) (R beta : R3 → ℝ)
    (x : R3) (C0 C1 M : ℝ) (hb : 0 ≤ beta x)
    (h : ContDiffAt ℝ ∞ f x ∧ ‖f x‖ ≤ C0*(R x)^2 ∧
      ‖fderiv ℝ f x‖ ≤ C1*(R x)^2*(beta x))
    (hC0 : C0 ≤ M) (hC1 : C1 ≤ M) : FirstCaps f R beta M x := by
  refine ⟨h.1,h.2.1.trans (mul_le_mul_of_nonneg_right hC0 (sq_nonneg _)),?_⟩
  exact h.2.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC1 (sq_nonneg _)) hb)

/-- The complete weighted physical-profile construction is elaborated once,
independently of any actual Sobolev endpoint body. -/
private lemma physical_profile_weighted_firstCaps
    (g : MatrixField) (L dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (weight : Fin 3 → R3 → ℝ)
    (E : Fin 3 → ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) → V)
    (Ma B0 KT J : ℝ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hMa : 0 ≤ Ma) (hB0 : 0 ≤ B0) (hKT : 0 ≤ KT) (hJ : 0 ≤ J)
    (hWeight : ∀ i,ContDiffAt ℝ ∞ (weight i) x ∧ |weight i x| ≤ Ma ∧
      ‖fderiv ℝ (weight i) x‖ ≤ Ma)
    (hE : ∀ i,physicalEndpointFirstCaps (L := L) (E i) dr Ar p q x B0 KT)
    (hR : ContDiffAt ℝ ∞ (referenceRadius dr Ar p L) x)
    (hR0 : 0 ≤ referenceRadius dr Ar p L x)
    (hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    FirstCaps (fun y => (referenceRadius dr Ar p L y)^2 •
      ∑ i : Fin 3,weight i y • E i (ActualHigherSFormation.higherSParam L dr Ar p q y))
      (referenceRadius dr Ar p L) (actualReferenceBeta g L q dr Ar p)
      (3*Ma*B0+3*Ma*(2*J*B0+B0+B0*KT)+1) x := by
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p
  let M : ℝ := 3*Ma*B0+3*Ma*(2*J*B0+B0+B0*KT)+1
  have hB1 : 0 ≤ B0*KT := mul_nonneg hB0 hKT
  have h := radius_squared_weighted_first_caps R weight
    (fun i y => E i (ActualHigherSFormation.higherSParam L dr Ar p q y)) x (beta x)
    Ma B0 (B0*KT) J hb hMa hB0 hB1 hJ hR0 hR
    (fun i => (hWeight i).1) (fun i => (hE i).1)
    (fun i => by simpa only [Real.norm_eq_abs] using (hWeight i).2.1)
    (fun i => (hWeight i).2.2) (fun i => (hE i).2.1) (fun i => (hE i).2.2) hR1
  have hc0 : 0 ≤ 3*Ma*B0 := by positivity
  have hc1 : 0 ≤ 3*Ma*(2*J*B0+B0+B0*KT) := by positivity
  have hC0 : 3*Ma*B0 ≤ M := by dsimp only [M]; linarith only [hc1]
  have hC1 : 3*Ma*(2*J*B0+B0+B0*KT) ≤ M := by dsimp only [M]; linarith only [hc0]
  exact firstCaps_of_bounds _ R beta x _ _ M (zero_le_one.trans hb) h hC0 hC1

lemma firstCaps_neg (f : R3 → V) (R beta : R3 → ℝ) (M : ℝ) (x : R3)
    (h : FirstCaps f R beta M x) : FirstCaps (fun y => -f y) R beta M x := by
  refine ⟨h.1.neg,?_,?_⟩
  · simpa only [norm_neg] using h.2.1
  · change ‖fderiv ℝ (-f) x‖ ≤ M*(R x)^2*(beta x)
    rw [fderiv_neg,norm_neg]
    exact h.2.2
end Generic

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
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh sphereSobolevInclusionL

/-- Function identity extracted from the checked physical contraction tuple. -/
private lemma actual_high_first_function (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (k : Fin 3) :
    (fun y => PH g2 dr Ar p q y k)=
      (fun y => (referenceRadius dr Ar p L y)^2 • ∑ i : Fin 3,
        firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • EH i ((Tq dr Ar p q) y)) := by
  funext y
  exact (ActualPPLowerRemainder.actual_first_coordinate_contractions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y k).1

private lemma actual_low_first_function (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (k : Fin 3) :
    (fun y => PL g2 dr Ar p q y k)=
      (fun y => (referenceRadius dr Ar p L y)^2 • ∑ i : Fin 3,
        firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • EL i ((Tq dr Ar p q) y)) := by
  funext y
  exact (ActualPPLowerRemainder.actual_first_coordinate_contractions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y k).2.1

private lemma actual_reverse_high_first_function (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (k : Fin 3) :
    (fun y => DH g2 dr Ar p q y k)=
      (fun y => -((referenceRadius dr Ar p L y)^2 • ∑ i : Fin 3,
        firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BH i ((Tq dr Ar p q) y))) := by
  funext y
  have hc := (ActualPPLowerRemainder.actual_first_coordinate_contractions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y k).2.2.1
  have hSign : (-(referenceRadius dr Ar p L y)^2) •
      (∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BH i ((Tq dr Ar p q) y))=
      -((referenceRadius dr Ar p L y)^2 •
      (∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BH i ((Tq dr Ar p q) y))) :=
    neg_smul ((referenceRadius dr Ar p L y)^2)
      (show SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) from
        ∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BH i ((Tq dr Ar p q) y))
  exact hc.trans hSign

private lemma actual_reverse_low_first_function (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (k : Fin 3) :
    (fun y => DL g2 dr Ar p q y k)=
      (fun y => -((referenceRadius dr Ar p L y)^2 • ∑ i : Fin 3,
        firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BL i ((Tq dr Ar p q) y))) := by
  funext y
  have hc := (ActualPPLowerRemainder.actual_first_coordinate_contractions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y k).2.2.2
  have hSign : (-(referenceRadius dr Ar p L y)^2) •
      (∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BL i ((Tq dr Ar p q) y))=
      -((referenceRadius dr Ar p L y)^2 •
      (∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BL i ((Tq dr Ar p q) y))) :=
    neg_smul ((referenceRadius dr Ar p L y)^2)
      (show SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) from
        ∑ i : Fin 3,firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y) • BL i ((Tq dr Ar p q) y))
  exact hc.trans hSign

attribute [local irreducible] FirstCaps

/-- Actual high endpoint cap from its OWN original physical cap projection. -/
private lemma actual_high_first_caps_at
    (Ma J : ℝ) (hMa : 0 ≤ Ma) (hJ : 0 ≤ J) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (k : Fin 3)
    (hWeight : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)| ≤ Ma ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x‖ ≤ Ma)
    (hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    FirstCaps (fun y => PH g2 dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p)
      (3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1) x := by
  let weight : Fin 3 → R3 → ℝ := fun i y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p
  let M : ℝ := 3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hR : ContDiffAt ℝ ∞ R x :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have hR0 : 0 ≤ R x := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hCaps : FirstCaps
      (fun y => (R y)^2 • ∑ i : Fin 3,weight i y • EH i ((Tq dr Ar p q) y)) R beta M x :=
    physical_profile_weighted_firstCaps g L dr Ar p q x weight EH
      Ma data.M data.KT J hb hMa data.M_nonneg data.KT_pos.le hJ hWeight
      (fun i => (he i).2.2.1) hR hR0 hR1
  have hFn := actual_high_first_function
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q k
  exact (congrArg (fun f => FirstCaps f R beta M x) hFn).mpr hCaps

/-- Actual low endpoint cap from its OWN original physical cap projection. -/
private lemma actual_low_first_caps_at
    (Ma J : ℝ) (hMa : 0 ≤ Ma) (hJ : 0 ≤ J) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (k : Fin 3)
    (hWeight : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)| ≤ Ma ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x‖ ≤ Ma)
    (hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    FirstCaps (fun y => PL g2 dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p)
      (3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1) x := by
  let weight : Fin 3 → R3 → ℝ := fun i y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p
  let M : ℝ := 3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hR : ContDiffAt ℝ ∞ R x :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have hR0 : 0 ≤ R x := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hCaps : FirstCaps
      (fun y => (R y)^2 • ∑ i : Fin 3,weight i y • EL i ((Tq dr Ar p q) y)) R beta M x :=
    physical_profile_weighted_firstCaps g L dr Ar p q x weight EL
      Ma data.M data.KT J hb hMa data.M_nonneg data.KT_pos.le hJ hWeight
      (fun i => (he i).2.2.2.1) hR hR0 hR1
  have hFn := actual_low_first_function
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q k
  exact (congrArg (fun f => FirstCaps f R beta M x) hFn).mpr hCaps

/-- Actual reverse_high endpoint cap from its OWN original physical cap projection. -/
private lemma actual_reverse_high_first_caps_at
    (Ma J : ℝ) (hMa : 0 ≤ Ma) (hJ : 0 ≤ J) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (k : Fin 3)
    (hWeight : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)| ≤ Ma ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x‖ ≤ Ma)
    (hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    FirstCaps (fun y => DH g2 dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p)
      (3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1) x := by
  let weight : Fin 3 → R3 → ℝ := fun i y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p
  let M : ℝ := 3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hR : ContDiffAt ℝ ∞ R x :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have hR0 : 0 ≤ R x := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hCaps : FirstCaps
      (fun y => (R y)^2 • ∑ i : Fin 3,weight i y • BH i ((Tq dr Ar p q) y)) R beta M x :=
    physical_profile_weighted_firstCaps g L dr Ar p q x weight BH
      Ma data.M data.KT J hb hMa data.M_nonneg data.KT_pos.le hJ hWeight
      (fun i => (he i).2.2.2.2.1) hR hR0 hR1
  have hFn := actual_reverse_high_first_function
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q k
  have hNeg := firstCaps_neg _ R beta M x hCaps
  exact (congrArg (fun f => FirstCaps f R beta M x) hFn).mpr hNeg

/-- Actual reverse_low endpoint cap from its OWN original physical cap projection. -/
private lemma actual_reverse_low_first_caps_at
    (Ma J : ℝ) (hMa : 0 ≤ Ma) (hJ : 0 ≤ J) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (k : Fin 3)
    (hWeight : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)| ≤ Ma ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x‖ ≤ Ma)
    (hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    FirstCaps (fun y => DL g2 dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p)
      (3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1) x := by
  let weight : Fin 3 → R3 → ℝ := fun i y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p
  let M : ℝ := 3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1
  have he (i : Fin 3) := data.physical_caps
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have hR : ContDiffAt ℝ ∞ R x :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have hR0 : 0 ≤ R x := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hCaps : FirstCaps
      (fun y => (R y)^2 • ∑ i : Fin 3,weight i y • BL i ((Tq dr Ar p q) y)) R beta M x :=
    physical_profile_weighted_firstCaps g L dr Ar p q x weight BL
      Ma data.M data.KT J hb hMa data.M_nonneg data.KT_pos.le hJ hWeight
      (fun i => (he i).2.2.2.2.2) hR hR0 hR1
  have hFn := actual_reverse_low_first_function
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q k
  have hNeg := firstCaps_neg _ R beta M x hCaps
  exact (congrArg (fun f => FirstCaps f R beta M x) hFn).mpr hNeg

/-- All four actual first-coefficient caps derive from the original endpoint
record, scalar weights and radius jets; constants precede every profile. -/
theorem exists_actual_first_coefficient_caps (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ M : ℝ, 0 < M ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ k : Fin 3,
      FirstCaps (fun y => PH g2 dr Ar p q y k) (referenceRadius dr Ar p L)
        (actualReferenceBeta g L q dr Ar p) M x ∧
      FirstCaps (fun y => PL g2 dr Ar p q y k) (referenceRadius dr Ar p L)
        (actualReferenceBeta g L q dr Ar p) M x ∧
      FirstCaps (fun y => DH g2 dr Ar p q y k) (referenceRadius dr Ar p L)
        (actualReferenceBeta g L q dr Ar p) M x ∧
      FirstCaps (fun y => DL g2 dr Ar p q y k) (referenceRadius dr Ar p L)
        (actualReferenceBeta g L q dr Ar p) M x := by
  obtain ⟨Ma,hMa,hweights⟩ := exists_physical_firstCoordinateWeight_uniform_first_caps
    g g2 hg hg2 L y0 ρ
  obtain ⟨J,hJ,hjet⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _) 1
  let M : ℝ := 3*Ma*data.M+3*Ma*(2*J*data.M+data.M+data.M*data.KT)+1
  have hMa0 : 0 ≤ Ma := zero_le_one.trans hMa
  have hBM : 0 ≤ data.M := data.M_nonneg
  have hKT : 0 < data.KT := data.KT_pos
  have hMpos : 0 < M := by dsimp only [M]; positivity
  refine ⟨M,hMpos,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs k
  have hWeight (i : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)| ≤ Ma ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) y)) x‖ ≤ Ma :=
    ⟨(hweights q hq x hx dr Ar p k i).1.contDiffAt,(hweights q hq x hx dr Ar p k i).2⟩
  have hR1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x := by
    simpa only [norm_iteratedFDeriv_one,pow_one,actualReferenceBeta] using
      (hjet q hq dr hdr hdr1 Ar hAr p hp x hx).1
  exact ⟨actual_high_first_caps_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      Ma J hMa0 hJ.le g2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs k hWeight hR1,
    actual_low_first_caps_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      Ma J hMa0 hJ.le g2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs k hWeight hR1,
    actual_reverse_high_first_caps_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      Ma J hMa0 hJ.le g2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs k hWeight hR1,
    actual_reverse_low_first_caps_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      Ma J hMa0 hJ.le g2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs k hWeight hR1⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPCoefficientCaps
