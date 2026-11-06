import Calderon.ActualHigherSLinearZeroDensityCaps
/-! Uniform O(r² beta) linear-zero high caps from original endpoint data.
UNCOMPILED author source. Full before-code expansion: linear-zero-caps-upfront-v001. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZero
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ActualHigherSLinearZeroScalarCaps ActualHigherSLinearZeroDensityCaps
  ActualHigherSLeadingWeightedJetBounds ConformalDepth PrincipalCommutator
open SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section NormAlgebra
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma norm_three_sum_le (v : Fin 3 → V) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ‖∑ i : Fin 3,v i‖ ≤ 3*C := by
  calc
    _ ≤ ∑ i : Fin 3,‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3,C := Finset.sum_le_sum (fun i _ => hv i)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

lemma norm_linear_row_le (d : V) (e : Fin 3 → V) (f : ℝ) (Gamma : Fin 3 → ℝ)
    (j : Fin 3) (S E A beta : ℝ) (hS : 0 ≤ S) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hb : 1 ≤ beta) (hd : ‖d‖ ≤ A) (he : ∀ k,‖e k‖ ≤ E)
    (hf : |f| ≤ S*beta) (hG : ∀ k,|Gamma k| ≤ S) :
    ‖d+f • e j-∑ k : Fin 3,Gamma k • e k‖ ≤ (A+4*S*E)*beta := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hsum : ‖∑ k : Fin 3,Gamma k • e k‖ ≤ 3*(S*E) :=
    norm_three_sum_le _ _ (fun k => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hG k) (he k) (norm_nonneg _) hS)
  have hfe : ‖f • e j‖ ≤ (S*beta)*E := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hf (he j) (norm_nonneg _) (mul_nonneg hS hb0)
  have hAb : A ≤ A*beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hA
  have hSEb : S*E ≤ S*E*beta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (mul_nonneg hS hE)
  calc
    _ ≤ (‖d‖+‖f • e j‖)+‖∑ k : Fin 3,Gamma k • e k‖ :=
      (norm_sub_le (d+f • e j) (∑ k : Fin 3,Gamma k • e k)).trans
        (add_le_add (norm_add_le d (f • e j))
          (le_refl ‖∑ k : Fin 3,Gamma k • e k‖))
    _ ≤ (A+(S*beta)*E)+3*(S*E) := add_le_add (add_le_add hd hfe) hsum
    _ ≤ (A+4*S*E)*beta := by nlinarith only [hAb,hSEb]

/-- All nine coefficient rows and all three drift rows remain in their order. -/
lemma norm_linear_family_le (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (f b : Fin 3 → ℝ) (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (e : Fin 3 → V) (d : Fin 3 → Fin 3 → V) (S E A beta : ℝ)
    (hS : 0 ≤ S) (hE : 0 ≤ E) (hA : 0 ≤ A) (hb : 1 ≤ beta)
    (hQ : ∀ i j,|Q i j| ≤ S) (hf : ∀ i,|f i| ≤ S*beta)
    (hG : ∀ i k j,|Gamma i k j| ≤ S) (hbval : ∀ i,|b i| ≤ S)
    (he : ∀ i,‖e i‖ ≤ E) (hd : ∀ i j,‖d i j‖ ≤ A) :
    ‖r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
      (d i j+f i • e j-∑ k : Fin 3,Gamma i k j • e k))+
      r^2 • (∑ i : Fin 3,b i • e i)‖ ≤
      (9*S*(A+4*S*E)+3*S*E)*r^2*beta := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hrow0 : 0 ≤ (A+4*S*E)*beta := by positivity
  have hrows : ‖∑ i : Fin 3,∑ j : Fin 3,Q i j •
      (d i j+f i • e j-∑ k : Fin 3,Gamma i k j • e k)‖ ≤ 9*(S*((A+4*S*E)*beta)) :=
    norm_double_sum_le _ _ (fun i j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hQ i j)
        (norm_linear_row_le _ e (f i) (fun k => Gamma i k j) j S E A beta hS hE hA hb
          (hd i j) he (hf i) (fun k => hG i k j)) (norm_nonneg _) hS)
  have hdrift : ‖∑ i : Fin 3,b i • e i‖ ≤ 3*(S*E) :=
    norm_three_sum_le _ _ (fun i => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hbval i) (he i) (norm_nonneg _) hS)
  have hdb : 3*(S*E) ≤ 3*(S*E)*beta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3*(S*E))
  calc
    _ ≤ ‖r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
      (d i j+f i • e j-∑ k : Fin 3,Gamma i k j • e k))‖+
      ‖r^2 • (∑ i : Fin 3,b i • e i)‖ := norm_add_le _ _
    _ ≤ r^2*(9*(S*((A+4*S*E)*beta)))+r^2*(3*(S*E)*beta) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      exact add_le_add (mul_le_mul_of_nonneg_left hrows (sq_nonneg _))
        (mul_le_mul_of_nonneg_left (hdrift.trans hdb) (sq_nonneg _))
    _ = _ := by ring

lemma norm_density_rows_le (r beta D E : ℝ) (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (e : Fin 3 → V) (hD : 0 ≤ D) (hE : 0 ≤ E) (hb : 0 ≤ beta)
    (hd1 : ∀ i j,|d1 i j| ≤ D*r^2*beta) (hd2 : ∀ i j,|d2 i j| ≤ D*r^2*beta)
    (he : ∀ i,‖e i‖ ≤ E) :
    ‖∑ i : Fin 3,∑ j : Fin 3,(d1 i j • e j+d2 i j • e i)‖ ≤ 18*D*E*r^2*beta := by
  have hrow (i j : Fin 3) : ‖d1 i j • e j+d2 i j • e i‖ ≤ 2*((D*r^2*beta)*E) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    have h1 := mul_le_mul (hd1 i j) (he j) (norm_nonneg _) (by positivity : 0 ≤ D*r^2*beta)
    have h2 := mul_le_mul (hd2 i j) (he i) (norm_nonneg _) (by positivity : 0 ≤ D*r^2*beta)
    linarith only [h1,h2]
  exact (norm_double_sum_le _ _ hrow).trans (le_of_eq (by ring))
end NormAlgebra

private lemma norm_neg_operator_apply_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : R3 →L[ℝ] V →L[ℝ] W) (X : R3) : ‖(-D) X‖=‖D X‖ := by
  have hApply : (-D) X=-(D X) := rfl
  rw [hApply]
  exact ContinuousLinearMap.opNorm_neg (D X)

private lemma operator_norm_sub_le {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (P R : V →L[ℝ] W) : ‖P-R‖ ≤ ‖P‖+‖R‖ := by
  have h := ContinuousLinearMap.opNorm_add_le (f := P) (g := -R)
  simpa only [sub_eq_add_neg,ContinuousLinearMap.opNorm_neg] using h

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
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z1" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Uniform scalar and original endpoint caps discharge every quantitative premise. -/
theorem exists_linear_zero_high_bound (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CL : ℝ,0 < CL ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,
      ∀ p : ℕ,1 ≤ p → ∀ eta : ℝ,0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ,x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ‖Z1 g2 dr Ar p q x‖ ≤ CL*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x ∧
      ‖T1 g2 dr Ar p q x‖ ≤ CL*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x := by
  obtain ⟨S,hS,hscalar⟩ := exists_word_scalar_caps g hg L hL y0 ρ g2 hg2
  obtain ⟨D,hDpos,hden⟩ := exists_normalized_second_derivative_cap g hg L hL y0 ρ g2 hg2
  let E : ℝ := data.M
  let A : ℝ := data.M*data.KT*S
  let C0 : ℝ := 9*S*(A+4*S*E)+3*S*E
  let CL : ℝ := 1+C0+18*D*E
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hE0 : 0 ≤ E := data.M_nonneg
  have hA0 : 0 ≤ A :=
    mul_nonneg (mul_nonneg data.M_nonneg data.KT_pos.le) hS0
  have hC00 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hDE : 0 ≤ 18*D*E := by positivity
  have hCLsum : 0 ≤ C0+18*D*E := add_nonneg hC00 hDE
  have hCL : 0 < CL := by dsimp only [CL]; linarith only [hCLsum]
  have hC0CL : C0 ≤ CL := by dsimp only [CL]; linarith
  have hCTCL : C0+18*D*E ≤ CL := by dsimp only [CL]; linarith
  refine ⟨CL,hCL,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let e : Fin 3 → Hi →L[ℝ] Half := fun i => EH i ((Tq dr Ar p q) x)
  let b : Fin 3 → Hi →L[ℝ] Half := fun i => BH i ((Tq dr Ar p q) x)
  let X := referenceMetricGramFrame g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  let drift := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let dE := fun i j => fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x (X i)
  let dB := fun i j => -(fderiv ℝ (fun y => BH i ((Tq dr Ar p q) y)) x (X j))
  let d1 := fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x
  let d2 := fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x
  have hsc := hscalar q hq dr hdr hdr1 Ar hAr p hp x hx hb
  have hcap (i : Fin 3) := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i 0
  have he (i : Fin 3) : ‖e i‖ ≤ E := (hcap i).2.2.1.2.1
  have hbval (i : Fin 3) : ‖b i‖ ≤ E := (hcap i).2.2.2.2.1.2.1
  have hde (i j : Fin 3) : ‖dE i j‖ ≤ A :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul ((hcap j).2.2.1.2.2) (hsc.2.2.2.1 i) (norm_nonneg _) (mul_nonneg data.M_nonneg data.KT_pos.le))
  have hdb (i j : Fin 3) : ‖dB i j‖ ≤ A := by
    let Df : R3 →L[ℝ] Hi →L[ℝ] Half :=
      fderiv ℝ (fun y => BH i ((Tq dr Ar p q) y)) x
    have hValue : dB i j=(-Df) (X j) := rfl
    calc
      ‖dB i j‖ = ‖(-Df) (X j)‖ := congrArg (fun T : Hi →L[ℝ] Half => ‖T‖) hValue
      _ = ‖Df (X j)‖ := norm_neg_operator_apply_eq Df (X j)
      _ ≤ A := (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul ((hcap i).2.2.2.2.1.2.2) (hsc.2.2.2.1 j) (norm_nonneg _)
          (mul_nonneg data.M_nonneg data.KT_pos.le))
  have hz := norm_linear_family_le r Q f drift Gamma e dE S E A beta hS0 hE0 hA0 hb
    hsc.1 hsc.2.2.1 hsc.2.1 hsc.2.2.2.2 he hde
  have ht := norm_linear_family_le r Q f drift Gamma b dB S E A beta hS0 hE0 hA0 hb
    hsc.1 hsc.2.2.1 hsc.2.1 hsc.2.2.2.2 hbval hdb
  have hds := norm_density_rows_le r beta D E d1 d2 b hDpos.le hE0 (zero_le_one.trans hb)
    (fun i j => hden q hq dr hdr hdr1 Ar hAr p hp x hx hb i j i)
    (fun i j => hden q hq dr hdr hdr1 Ar hAr p hp x hx hb i j j) hbval
  have hscale : 0 ≤ r^2*beta := mul_nonneg (sq_nonneg _) (zero_le_one.trans hb)
  refine ⟨hz.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0CL (sq_nonneg _))
      (zero_le_one.trans hb)
  · have htform : T1 g2 dr Ar p q x =
        (r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
          (dB i j+f i • b j-∑ k : Fin 3,Gamma i k j • b k))+
          r^2 • (∑ i : Fin 3,drift i • b i))-
        ∑ i : Fin 3,∑ j : Fin 3,(d1 i j • b j+d2 i j • b i) := by
      dsimp only [linearAdjointZeroHigh,r,Q,f,Gamma,drift,dB,b,d1,d2,X]
      abel
    let mainPart : Hi →L[ℝ] Half :=
      r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j •
        (dB i j+f i • b j-∑ k : Fin 3,Gamma i k j • b k))+
        r^2 • (∑ i : Fin 3,drift i • b i)
    let densityPart : Hi →L[ℝ] Half :=
      ∑ i : Fin 3,∑ j : Fin 3,(d1 i j • b j+d2 i j • b i)
    have hMain : ContinuousLinearMap.opNorm
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) mainPart ≤ C0*r^2*beta := ht
    have hDensity : ContinuousLinearMap.opNorm
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) densityPart ≤ 18*D*E*r^2*beta := hds
    have hTriangle : ContinuousLinearMap.opNorm
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) (mainPart-densityPart) ≤
        ContinuousLinearMap.opNorm (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) mainPart+
        ContinuousLinearMap.opNorm (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) densityPart :=
      operator_norm_sub_le mainPart densityPart
    have hOperatorBound : ContinuousLinearMap.opNorm
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) (mainPart-densityPart) ≤
        C0*r^2*beta+18*D*E*r^2*beta := hTriangle.trans (add_le_add hMain hDensity)
    have hRealBound : C0*r^2*beta+18*D*E*r^2*beta ≤ CL*r^2*beta := by
      calc
        _ = (C0+18*D*E)*(r^2*beta) := by ring
        _ ≤ CL*(r^2*beta) := mul_le_mul_of_nonneg_right hCTCL hscale
        _ = CL*r^2*beta := by ring
    rw [htform]
    change ContinuousLinearMap.opNorm
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ) (mainPart-densityPart) ≤ CL*r^2*beta
    exact hOperatorBound.trans hRealBound

/-- Exact original contract: constants and threshold precede all profiles and inputs. -/
def LinearZeroHighContract (g2 : MatrixField) : Prop :=
  ∃ CLinear etaLinear : ℝ,0 < CLinear ∧ 0 < etaLinear ∧ etaLinear ≤ data.eta0 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,
    ∀ p : ℕ,1 ≤ p → ∀ eta : ℝ,0 ≤ eta → eta ≤ etaLinear →
    ∀ K : Set R3,IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD,tsupport F.val ⊆ K →
    (∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K,
      ContDiffAt ℝ ∞ (Z1 g2 dr Ar p q) x ∧ ContDiffAt ℝ ∞ (T1 g2 dr Ar p q) x ∧
      ‖Z1 g2 dr Ar p q x‖ ≤ CLinear*(referenceRadius dr Ar p L x)^2*(actualReferenceBeta g L q dr Ar p x) ∧
      ‖T1 g2 dr Ar p q x‖ ≤ CLinear*(referenceRadius dr Ar p L x)^2*(actualReferenceBeta g L q dr Ar p x)) ∧
    ContDiff ℝ ∞ (fun x => Z1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    ContDiff ℝ ∞ (fun x => T1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    HasCompactSupport (fun x => Z1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x)) ∧
    HasCompactSupport (fun x => T1 g2 dr Ar p q x (ActualHigherSFormation.higherSInput hO hD F x))

theorem exists_linear_zero_high_contract (hL : 0 < L) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    LinearZeroHighContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 := by
  obtain ⟨CL,hCL,hbound⟩ := exists_linear_zero_high_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  refine ⟨CL,data.eta0,hCL,data.eta0_pos,le_refl _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  have hsm := linear_zero_high_outputs_smooth_compact
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  refine ⟨?_,hsm⟩
  intro x hx
  have hcd := linear_zero_high_contDiffAt
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x
    (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
  exact ⟨hcd.1,hcd.2,hbound q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x
    (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZero
