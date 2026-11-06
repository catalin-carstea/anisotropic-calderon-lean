import Calderon.ActualPPCoefficientCaps
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSAdjointFormation
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPBalancedBound
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
  ActualPPCoefficientCaps ActualHigherSLeadingWeightedJetBounds SectionFiveErrorForms
  ActualScalarPrincipalSelfFormBound
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
/-- The existing standard operator norm at the concrete dual-pairing endpoint. -/
@[instance_reducible, instance] def halfNegativePairingOperatorNorm :
    Norm (Half →L[ℝ] Neg →L[ℝ] ℝ) where
  norm P := ContinuousLinearMap.opNorm
    (E := Half) (F := Neg →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ) P

lemma halfNegativePairingOperatorNorm_norm_def (P : Half →L[ℝ] Neg →L[ℝ] ℝ) :
    @Norm.norm _ halfNegativePairingOperatorNorm P=
      ContinuousLinearMap.opNorm
        (E := Half) (F := Neg →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ) P := rfl

private lemma halfNegativePairingOperatorNorm_nonneg (P : Half →L[ℝ] Neg →L[ℝ] ℝ) :
    0 ≤ ‖P‖ := by
  change 0 ≤ sInf {c : ℝ | 0 ≤ c ∧ ∀ v : Half, ‖P v‖ ≤ c*‖v‖}
  exact Real.sInf_nonneg (fun _ h => h.1)

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
  (g2 : MatrixField)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "HU" => ActualHigherSScalarCommutatorNativeForm.halfInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Lead" => actualLeadingSignedSecondNeg
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2


local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "BR" => ActualPPLowerRemainder.actualPPBalancedRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

private lemma pair_low_high_of_caps {E H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : H →L[ℝ] N →L[ℝ] ℝ) (Low : H →L[ℝ] N) (High : E →L[ℝ] H)
    (u : E) (v : H) (L0 A0 : ℝ) (hL0 : 0 ≤ L0) (hA0 : 0 ≤ A0)
    (hLow : ‖Low‖ ≤ L0) (hHigh : ‖High‖ ≤ A0) :
    |P v (Low (High u))| ≤ ‖P‖*L0*A0*(‖u‖*‖v‖) := by
  have hAu : ‖High u‖ ≤ A0*‖u‖ :=
    (High.le_opNorm u).trans (mul_le_mul_of_nonneg_right hHigh (norm_nonneg _))
  have hLAu : ‖Low (High u)‖ ≤ L0*(A0*‖u‖) :=
    (Low.le_opNorm (High u)).trans (mul_le_mul hLow hAu (norm_nonneg _) hL0)
  calc
    _ ≤ ‖P‖*‖v‖*‖Low (High u)‖ := by
      simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P v (Low (High u))
    _ ≤ ‖P‖*‖v‖*(L0*(A0*‖u‖)) :=
      mul_le_mul_of_nonneg_left hLAu (by positivity)
    _ = _ := by ring

private lemma six_term_abs_bound (mu beta Md H U dk dl a b c d e f dmL dmK : ℝ)
    (hmu : 0 ≤ mu) (hb : 0 ≤ beta) (hMd : 0 ≤ Md) (hH : 0 ≤ H)
    (hU : 0 ≤ U) (hdk : 0 ≤ dk) (hdl : 0 ≤ dl)
    (ha : |a| ≤ H*beta*U*dk) (hb' : |b| ≤ H*beta*U*dk)
    (hc : |c| ≤ H*beta*U*dl) (hd : |d| ≤ H*beta*U*dl)
    (he : |e| ≤ H*U*dk) (hf : |f| ≤ H*U*dl)
    (hmL : |dmL| ≤ Md*mu) (hmK : |dmK| ≤ Md*mu) :
    |mu*(a+b-c-d)+dmL*e-dmK*f| ≤ mu*H*(2*beta+Md)*U*(dk+dl) := by
  have hsum : |a+b-c-d| ≤ |a|+|b|+|c|+|d| :=
    (abs_sub (a+b-c) d).trans
      (add_le_add ((abs_sub (a+b) c).trans
        (add_le_add (abs_add_le a b) (le_refl |c|))) (le_refl |d|))
  calc
    _ ≤ |mu*(a+b-c-d)|+|dmL*e|+|dmK*f| :=
      (abs_sub (mu*(a+b-c-d)+dmL*e) (dmK*f)).trans
        (add_le_add (abs_add_le (mu*(a+b-c-d)) (dmL*e)) (le_refl |dmK*f|))
    _ ≤ mu*(|a|+|b|+|c|+|d|)+|dmL| *|e|+|dmK| *|f| := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hmu]
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hsum hmu) (le_refl (|dmL| *|e|)))
        (le_refl (|dmK| *|f|))
    _ ≤ mu*(H*beta*U*dk+H*beta*U*dk+H*beta*U*dl+H*beta*U*dl)+
        (Md*mu)*(H*U*dk)+(Md*mu)*(H*U*dl) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add ha hb') hc) hd) hmu)
        (mul_le_mul hmL he (abs_nonneg _) (by positivity)))
        (mul_le_mul hmK hf (abs_nonneg _) (by positivity))
    _ = _ := by ring

private lemma coordinate_derivative_cap {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : R3 → V) (x : R3) (i : Fin 3) (A : ℝ)
    (h : ‖fderiv ℝ f x‖ ≤ A) : ‖directionalFDeriv (coordinateDirection i) f x‖ ≤ A := by
  calc
    _ ≤ ‖fderiv ℝ f x‖*‖coordinateDirection i‖ := (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [ActualScalarPrincipalAdjoint.norm_coordinateDirection,mul_one]
    _ ≤ A := h

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Actual original-energy bound for each of the nine complete six-term
balanced rows. All coefficient/density/energy constants are produced here
from the original data before profiles, supports or angular inputs. -/
theorem exists_actual_balanced_row_point_bound (hL : 0 < L) (hg2 : IsAdmissibleMetric g2) :
    ∃ CRow : ℝ, 0 ≤ CRow ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ F : smoothCompactFiniteSphereCore hO hD, ∀ l k : Fin 3,
      |BR dr Ar p q F x l k| ≤ CRow*eta*referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨M,hM,hcaps⟩ := exists_actual_first_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨Md,hMd,hdmu⟩ := ActualHigherSScalarCommutatorNativeForm.exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cr,hCr,hcoord⟩ := ActualHigherSScalarCommutatorNativeForm.exists_halfInput_coordinate_reference_bound
    hO hD g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let N := ‖QPP‖
  let CRow := 2*N*M^2*(2+Md)*(1+Cr)
  have hMd0 : 0 ≤ Md := zero_le_one.trans hMd
  have hM0 : 0 ≤ M := hM.le
  have hN0 : 0 ≤ N := halfNegativePairingOperatorNorm_nonneg QPP
  have hCRow0 : 0 ≤ CRow := by dsimp [CRow]; positivity
  refine ⟨CRow,hCRow0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs F l k
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  let du : Fin 3 → Half := fun i => directionalFDeriv (coordinateDirection i) (HU F) x
  let mu := referenceDensityFamily g L (q,x)
  let E := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  let H0 := N*M^2*r^4
  have hr0 : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hbpos : 0 < beta := zero_lt_one.trans_le hb
  have hmu0 : 0 ≤ mu := (referenceDensityFamily_pos g hg L (q,x)).le
  have hE0 : 0 ≤ E := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q beta hb0 F x
  have hH0 : 0 ≤ H0 := by dsimp [H0]; positivity
  have hc (i : Fin 3) := hcaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i
  have hPH (i : Fin 3) : ‖PH dr Ar p q x i‖ ≤ M*r^2 := (hc i).1.2.1
  have hPL (i : Fin 3) : ‖PL dr Ar p q x i‖ ≤ M*r^2 := (hc i).2.1.2.1
  have hDH (i : Fin 3) : ‖DH dr Ar p q x i‖ ≤ M*r^2 := (hc i).2.2.1.2.1
  have hDL (i : Fin 3) : ‖DL dr Ar p q x i‖ ≤ M*r^2 := (hc i).2.2.2.2.1
  have hdPH (a i : Fin 3) :
      ‖directionalFDeriv (coordinateDirection a) (fun y => PH dr Ar p q y i) x‖ ≤ M*r^2*beta :=
    coordinate_derivative_cap _ x a _ (hc i).1.2.2
  have hdPL (a i : Fin 3) :
      ‖directionalFDeriv (coordinateDirection a) (fun y => PL dr Ar p q y i) x‖ ≤ M*r^2*beta :=
    coordinate_derivative_cap _ x a _ (hc i).2.1.2.2
  have hdDH (a i : Fin 3) :
      ‖directionalFDeriv (coordinateDirection a) (fun y => DH dr Ar p q y i) x‖ ≤ M*r^2*beta :=
    coordinate_derivative_cap _ x a _ (hc i).2.2.1.2.2
  have hdDL (a i : Fin 3) :
      ‖directionalFDeriv (coordinateDirection a) (fun y => DL dr Ar p q y i) x‖ ≤ M*r^2*beta :=
    coordinate_derivative_cap _ x a _ (hc i).2.2.2.2.2
  have pair0 (Low : Half →L[ℝ] Neg) (High : Hi →L[ℝ] Half) (v : Half)
      (hLow : ‖Low‖ ≤ M*r^2) (hHigh : ‖High‖ ≤ M*r^2) :
      |PP v (Low (High U))| ≤ H0*‖U‖*‖v‖ := by
    have h := pair_low_high_of_caps QPP Low High U v (M*r^2) (M*r^2)
      (by positivity) (by positivity) hLow hHigh
    have hscale : ‖QPP‖*(M*r^2)*(M*r^2)*(‖U‖*‖v‖)=H0*‖U‖*‖v‖ := by
      dsimp only [H0,N]
      ring
    have hscaled := h.trans (le_of_eq hscale)
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hscaled
  have pairHighD (Low : Half →L[ℝ] Neg) (High : Hi →L[ℝ] Half) (v : Half)
      (hLow : ‖Low‖ ≤ M*r^2) (hHigh : ‖High‖ ≤ M*r^2*beta) :
      |PP v (Low (High U))| ≤ H0*beta*‖U‖*‖v‖ := by
    have h := pair_low_high_of_caps QPP Low High U v (M*r^2) (M*r^2*beta)
      (by positivity) (by positivity) hLow hHigh
    have hscale : ‖QPP‖*(M*r^2)*(M*r^2*beta)*(‖U‖*‖v‖)=H0*beta*‖U‖*‖v‖ := by
      dsimp only [H0,N]
      ring
    have hscaled := h.trans (le_of_eq hscale)
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hscaled
  have pairLowD (Low : Half →L[ℝ] Neg) (High : Hi →L[ℝ] Half) (v : Half)
      (hLow : ‖Low‖ ≤ M*r^2*beta) (hHigh : ‖High‖ ≤ M*r^2) :
      |PP v (Low (High U))| ≤ H0*beta*‖U‖*‖v‖ := by
    have h := pair_low_high_of_caps QPP Low High U v (M*r^2*beta) (M*r^2)
      (by positivity) (by positivity) hLow hHigh
    have hscale : ‖QPP‖*(M*r^2*beta)*(M*r^2)*(‖U‖*‖v‖)=H0*beta*‖U‖*‖v‖ := by
      dsimp only [H0,N]
      ring
    have hscaled := h.trans (le_of_eq hscale)
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hscaled
  have ha := pairHighD (DL dr Ar p q x k)
    (directionalFDeriv (coordinateDirection l) (fun y => PH dr Ar p q y l) x)
    (du k) (hDL k) (hdPH l l)
  have hb' := pairLowD
    (directionalFDeriv (coordinateDirection l) (fun y => DL dr Ar p q y k) x)
    (PH dr Ar p q x l) (du k) (hdDL l k) (hPH l)
  have hc' := pairHighD (PL dr Ar p q x l)
    (directionalFDeriv (coordinateDirection k) (fun y => DH dr Ar p q y k) x)
    (du l) (hPL l) (hdDH k k)
  have hd := pairLowD
    (directionalFDeriv (coordinateDirection k) (fun y => PL dr Ar p q y l) x)
    (DH dr Ar p q x k) (du l) (hdPL k l) (hDH k)
  have he := pair0 (DL dr Ar p q x k) (PH dr Ar p q x l) (du k) (hDL k) (hPH l)
  have hf := pair0 (PL dr Ar p q x l) (DH dr Ar p q x k) (du l) (hPL l) (hDH k)
  let a0 : ℝ := PP (du k) (DL dr Ar p q x k
    ((directionalFDeriv (coordinateDirection l) (fun y => PH dr Ar p q y l) x) U))
  let b0 : ℝ := PP (du k)
    ((directionalFDeriv (coordinateDirection l) (fun y => DL dr Ar p q y k) x)
      (PH dr Ar p q x l U))
  let c0 : ℝ := PP (du l) (PL dr Ar p q x l
    ((directionalFDeriv (coordinateDirection k) (fun y => DH dr Ar p q y k) x) U))
  let d0 : ℝ := PP (du l)
    ((directionalFDeriv (coordinateDirection k) (fun y => PL dr Ar p q y l) x)
      (DH dr Ar p q x k U))
  let e0 : ℝ := PP (du k) (DL dr Ar p q x k (PH dr Ar p q x l U))
  let f0 : ℝ := PP (du l) (PL dr Ar p q x l (DH dr Ar p q x k U))
  let dmL : ℝ := directionalFDeriv (coordinateDirection l)
    (fun y : R3 => referenceDensityFamily g L (q,y)) x
  let dmK : ℝ := directionalFDeriv (coordinateDirection k)
    (fun y : R3 => referenceDensityFamily g L (q,y)) x
  have ha0 : |a0| ≤ H0*beta*‖U‖*‖du k‖ := ha
  have hb0' : |b0| ≤ H0*beta*‖U‖*‖du k‖ := hb'
  have hc0 : |c0| ≤ H0*beta*‖U‖*‖du l‖ := hc'
  have hd0 : |d0| ≤ H0*beta*‖U‖*‖du l‖ := hd
  have he0 : |e0| ≤ H0*‖U‖*‖du k‖ := he
  have hf0 : |f0| ≤ H0*‖U‖*‖du l‖ := hf
  have hdmL : |dmL| ≤ Md*mu := hdmu q hq x hx l
  have hdmK : |dmK| ≤ Md*mu := hdmu q hq x hx k
  have hscalar : |mu*(a0+b0-c0-d0)+dmL*e0-dmK*f0| ≤
      mu*H0*(2*beta+Md)*‖U‖*(‖du k‖+‖du l‖) :=
    six_term_abs_bound mu beta Md H0 ‖U‖ ‖du k‖ ‖du l‖ a0 b0 c0 d0 e0 f0 dmL dmK
      hmu0 hb0 hMd0 hH0 (norm_nonneg U) (norm_nonneg (du k)) (norm_nonneg (du l))
      ha0 hb0' hc0 hd0 he0 hf0 hdmL hdmK
  have hrow : BR dr Ar p q F x l k=mu*(a0+b0-c0-d0)+dmL*e0-dmK*f0 := by
    unfold ActualPPLowerRemainder.actualPPBalancedRow
    rfl
  have hsum : |BR dr Ar p q F x l k| ≤ mu*H0*(2*beta+Md)*‖U‖*(‖du k‖+‖du l‖) := by
    rw [hrow]
    exact hscalar
  have hCoord := hcoord q hq x hx beta hb F
  have hHigh := ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hb0 F x
  let S : ℝ := ∑ i : Fin 3, ‖du i‖^2
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hInvS : beta⁻¹*S ≤ Cr*E := by
    have hh : beta⁻¹*S ≤ coordinateEnergyDensity coordinateDirection beta (HU F) x := by
      unfold coordinateEnergyDensity
      change beta⁻¹*S ≤ beta⁻¹*S+beta*‖HU F x‖^2
      exact le_add_of_nonneg_right (by positivity)
    exact hh.trans hCoord
  have hOne (i : Fin 3) : beta⁻¹*‖du i‖^2 ≤ Cr*E := by
    have hsq : ‖du i‖^2 ≤ S := by
      change ‖du i‖^2 ≤ ∑ j : Fin 3, ‖du j‖^2
      exact Finset.single_le_sum (f := fun j : Fin 3 => ‖du j‖^2)
        (fun j _ => sq_nonneg ‖du j‖) (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hb0)).trans hInvS
  have hYoung : ‖U‖*(‖du k‖+‖du l‖) ≤ 2*(1+Cr)*E := by
    calc
      _ = ‖du k‖*‖U‖+‖du l‖*‖U‖ := by ring
      _ ≤ (beta⁻¹*‖du k‖^2+beta*‖U‖^2)+(beta⁻¹*‖du l‖^2+beta*‖U‖^2) :=
        add_le_add (mul_le_weighted_sq beta ‖du k‖ ‖U‖ hbpos)
          (mul_le_weighted_sq beta ‖du l‖ ‖U‖ hbpos)
      _ ≤ (Cr*E+E)+(Cr*E+E) := add_le_add (add_le_add (hOne k) hHigh) (add_le_add (hOne l) hHigh)
      _ = _ := by ring
  have hMdBeta : 2*beta+Md ≤ (2+Md)*beta := by
    nlinarith only [mul_nonneg hMd0 (sub_nonneg.mpr hb)]
  have h4 : r^4*beta ≤ eta := (radius_four_absorption r beta eta hr0 hb (heta0.trans data.eta0_le) hs).2
  calc
    _ ≤ mu*H0*(2*beta+Md)*‖U‖*(‖du k‖+‖du l‖) := hsum
    _ ≤ mu*H0*((2+Md)*beta)*‖U‖*(‖du k‖+‖du l‖) := by gcongr
    _ = (mu*N*M^2*(2+Md))*(r^4*beta)*(‖U‖*(‖du k‖+‖du l‖)) := by dsimp [H0]; ring
    _ ≤ (mu*N*M^2*(2+Md))*eta*(2*(1+Cr)*E) := by gcongr
    _ = CRow*eta*mu*E := by dsimp [CRow]; ring
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPBalancedBound
