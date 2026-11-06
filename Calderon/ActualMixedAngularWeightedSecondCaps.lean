import Calderon.ActualMixedAngularPhysicalBounds
import Calderon.ActualHigherSLeadingWeightedJetBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualHigherSLeadingWeightedJetBounds
  ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain
  ActualFullEGainedAssembly ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection

/-- The precise scalar budget used below; no profile parameter is hidden in it. -/
def mixedCoefficientBudget (M B0 B1 J : ℝ) : ℝ :=
  (9*M^2*B0)+(9*(2*M^2*B0+M^2*B1)+2*J*(9*M^2*B0))

private lemma radius_square_absorption (r beta eta : ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ beta) (heta1 : eta ≤ 1) (hs : r*beta^2 ≤ eta) :
    r^2 ≤ eta/beta ∧ r^2*beta ≤ eta := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hbpos : 0 < beta := zero_lt_one.trans_le hb
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hr1 : r ≤ 1 := (le_mul_of_one_le_right hr hb2).trans (hs.trans heta1)
  have hbb : beta ≤ beta^2 := by nlinarith
  have hrbb : r*beta ≤ beta^2 :=
    (mul_le_mul_of_nonneg_right hr1 hb0).trans (by simpa only [one_mul] using hbb)
  have hh : r^2*beta ≤ eta := by
    calc
      _ = r*(r*beta) := by ring
      _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left hrbb hr
      _ ≤ eta := hs
  exact ⟨(le_div_iff₀ hbpos).2 hh,hh⟩

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All nine actual mixed rows, weighted by R² and the two original scalar coordinate factors. -/
def weightedMixedSecondCoefficient (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3) : E →L[ℝ] F :=
  (R x)^2 • (∑ i : Fin 3, ∑ j : Fin 3, (a i x*b j x) • G i j x)

/-- Exact R² smallness in the original beta^{-1} two-base form scale. -/
theorem weightedMixedSecondCoefficient_first_caps
    (M B0 B1 J : ℝ) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hJ : 0 ≤ J)
    (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (G i j) x)
    (h0a : ∀ i, ‖a i x‖ ≤ M) (h1a : ∀ i, ‖fderiv ℝ (a i) x‖ ≤ M)
    (h0b : ∀ j, ‖b j x‖ ≤ M) (h1b : ∀ j, ‖fderiv ℝ (b j) x‖ ≤ M)
    (h0G : ∀ i j, ‖G i j x‖ ≤ B0) (h1G : ∀ i j, ‖fderiv ℝ (G i j) x‖ ≤ B1)
    (beta eta : ℝ) (hr : 0 ≤ R x) (hbeta : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hsmall : R x*beta^2 ≤ eta) (hjet : ‖fderiv ℝ R x‖ ≤ J*R x*beta) :
    ContDiffAt ℝ ∞ (weightedMixedSecondCoefficient R a b G) x ∧
      ‖weightedMixedSecondCoefficient R a b G x‖ ≤ mixedCoefficientBudget M B0 B1 J*eta/beta ∧
      ‖fderiv ℝ (weightedMixedSecondCoefficient R a b G) x‖ ≤ mixedCoefficientBudget M B0 B1 J*eta := by
  let A := 9*M^2*B0
  let B := 9*(2*M^2*B0+M^2*B1)
  let Q := mixedCoefficientBudget M B0 B1 J
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAQ : A ≤ Q := by
    change A ≤ A+(B+2*J*A)
    exact le_add_of_nonneg_right (add_nonneg hB (by positivity))
  have hBQ : B+2*J*A ≤ Q := by
    change B+2*J*A ≤ A+(B+2*J*A)
    exact le_add_of_nonneg_left hA
  let W := fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y
  have hW : ContDiffAt ℝ ∞ W x := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact ((ha i).mul (hb j)).smul (hG i j)
  have hc := weighted_family_first_caps a b G x
    (fun i => (ha i).differentiableAt (by simp)) (fun j => (hb j).differentiableAt (by simp))
    (fun i j => (hG i j).differentiableAt (by simp)) M B0 B1 hM hB0 hB1 h0a h1a h0b h1b h0G h1G
  have hRD := hR.differentiableAt (by simp)
  have hR2 : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*R x*‖fderiv ℝ R x‖ := by
    have he := norm_fderiv_scalar_smul_le R R x hRD hRD
    rw [Real.norm_eq_abs,abs_of_nonneg hr] at he
    calc
      _ ≤ R x*‖fderiv ℝ R x‖+‖fderiv ℝ R x‖*R x := by simpa only [pow_two,smul_eq_mul] using he
      _ = _ := by ring
  have hD := norm_fderiv_scalar_smul_le (fun y => (R y)^2) W x (hRD.pow 2)
    (hW.differentiableAt (by simp))
  have hDcap : ‖fderiv ℝ (weightedMixedSecondCoefficient R a b G) x‖ ≤ (B+2*J*A)*(R x)^2*beta := by
    change ‖fderiv ℝ (fun y => (R y)^2 • W y) x‖ ≤ _
    have hRnorm : ‖(R x)^2‖=(R x)^2 := by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (R x))]
    have hR2jet : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*J*(R x)^2*beta :=
      hR2.trans ((mul_le_mul_of_nonneg_left hjet (by positivity)).trans_eq (by ring))
    have hb0 : 0 ≤ beta := zero_le_one.trans hbeta
    calc
      _ ≤ ‖(R x)^2‖*‖fderiv ℝ W x‖+‖fderiv ℝ (fun y => (R y)^2) x‖*‖W x‖ := hD
      _ ≤ (R x)^2*B+(2*J*(R x)^2*beta)*A := by
        rw [hRnorm]
        exact add_le_add (mul_le_mul_of_nonneg_left hc.2 (sq_nonneg _))
          (mul_le_mul hR2jet hc.1 (norm_nonneg _) (by positivity))
      _ ≤ (R x)^2*(B*beta)+(2*J*(R x)^2*beta)*A := by
        gcongr
        exact le_mul_of_one_le_right hB hbeta
      _ = _ := by ring
  have hAbs := radius_square_absorption (R x) beta eta hr hbeta heta1 hsmall
  refine ⟨(hR.pow 2).smul hW,?_,?_⟩
  · calc
      _ = (R x)^2*‖W x‖ := by simp only [weightedMixedSecondCoefficient,W,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (R x))]
      _ ≤ (R x)^2*A := mul_le_mul_of_nonneg_left hc.1 (sq_nonneg _)
      _ ≤ (eta/beta)*A := mul_le_mul_of_nonneg_right hAbs.1 hA
      _ ≤ (eta/beta)*Q := mul_le_mul_of_nonneg_left hAQ (div_nonneg heta (zero_le_one.trans hbeta))
      _ = _ := by ring
  · calc
      _ ≤ (B+2*J*A)*((R x)^2*beta) := by simpa only [mul_assoc] using hDcap
      _ ≤ (B+2*J*A)*eta := mul_le_mul_of_nonneg_left hAbs.2 (by positivity)
      _ ≤ Q*eta := mul_le_mul_of_nonneg_right hBQ heta
end Generic

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
attribute [local instance] ActualAngularPiDraft.v017PiHighComplete
  ActualAngularPiDraft.v017PiHalfComplete ActualAngularPiDraft.v017PiNegativeComplete
@[instance_reducible] private def weightedLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def weightedLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] weightedLowNormed weightedLowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => ActualFullEGainedEndpoints.CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

private lemma compact_finite_norm_cap {X V I : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [Fintype I] (K : Set X) (hK : IsCompact K)
    (f : I → X → V) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose c hc using fun i : I => hK.exists_bound_of_continuousOn (hf i)
  refine ⟨1+∑ i, |c i|,le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _)),?_⟩
  intro i x hx
  exact (hc i x hx).trans ((le_abs_self _).trans ((Finset.single_le_sum
    (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)))

/-- Metric frame entries have one uniform value/first-slice cap, before every profile. -/
lemma exists_metricFrame_uniform_first_caps (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (y0 : R3) (ρ : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i l : Fin 3,
      ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i l) ∧
      |referenceMetricGramFrame g L (q,x) i l| ≤ M ∧
      ‖fderiv ℝ (fun y => referenceMetricGramFrame g L (q,y) i l) x‖ ≤ M := by
  let f : (Fin 3 × Fin 3) → (ℝ × R3) → ℝ := fun z => fun t => referenceMetricGramFrame g L t z.1 z.2
  have hf (z : Fin 3 × Fin 3) : ContDiff ℝ ∞ (f z) :=
    ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L z.1 z.2
  let K := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M0,hM0,h0⟩ := compact_finite_norm_cap K hK f (fun z => (hf z).continuous.continuousOn)
  obtain ⟨M1,hM1,h1⟩ := compact_finite_norm_cap K hK (fun z => fderiv ℝ (f z))
    (fun z => ((hf z).fderiv_right (m := ∞) (by simp)).continuous.continuousOn)
  refine ⟨M0+M1,by linarith,?_⟩
  intro q hq x hx i l
  have h0' := h0 (i,l) (q,x) ⟨hq,hx⟩
  have h1' := h1 (i,l) (q,x) ⟨hq,hx⟩
  have hS := norm_fderiv_fixed_q_slice_le (f (i,l)) (hf (i,l)) q x M1
    (zero_le_one.trans hM1) h1'
  exact ⟨(hf (i,l)).comp (contDiff_const.prodMk contDiff_id),
    (by simpa only [Real.norm_eq_abs] using h0'.trans (le_add_of_nonneg_right (zero_le_one.trans hM1))),
    hS.trans (le_add_of_nonneg_left (zero_le_one.trans hM0))⟩

/-- Original frame and symmetric S first-coordinate weights multiply the genuine low mixed gain. -/
def mixedAngularSecondCoefficient (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Half →L[ℝ] Neg :=
  weightedMixedSecondCoefficient (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => data.Bl i j ((Tq dr Ar p q) y))

/-- Actual high parent of the same radius-squared gained coefficient. -/
def mixedAngularSecondHighCoefficient (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Hi →L[ℝ] Half :=
  weightedMixedSecondCoefficient (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg data.G δ0 W i j ((Tq dr Ar p q) y))

/-- Exact native upper graph for the weighted coefficient; no inverse inclusion. -/
lemma mixedAngularSecondCoefficient_upper_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ (ActualAngularHighDraft.commonRoom y0 ρ data.δ).prod
      (closedBall (0 : R3 →L[ℝ] ℝ) 1)) :
    (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k x).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (mixedAngularSecondHighCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
        hreg δ0 W data g2 dr Ar p q l k x) := by
  have hG (i j : Fin 3) (u : Hi) := congrArg (fun T : Hi →L[ℝ] Neg => T u)
    ((data.graphs i j ((Tq dr Ar p q) x) hx).2.2.1)
  apply ContinuousLinearMap.ext
  intro u
  simpa only [mixedAngularSecondCoefficient,mixedAngularSecondHighCoefficient,
    weightedMixedSecondCoefficient,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum] using
    congrArg (fun f : Fin 3 → Fin 3 → Neg => (referenceRadius dr Ar p L x)^2 •
      ∑ i : Fin 3, ∑ j : Fin 3, (referenceMetricGramFrame g L (q,x) i l*
        firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x)) • f i j)
      (funext (fun i => funext (fun j => hG i j u)))

private lemma use_scalar_family_cap {P : ℝ → Prop} {Result : Prop}
    (h : ∃ M : ℝ, 1 ≤ M ∧ P M)
    (use : ∀ M : ℝ, 1 ≤ M → P M → Result) : Result := by
  rcases h with ⟨M,hM,hP⟩
  exact use M hM hP

private theorem mixedAngularSecondCoefficient_pointwise_caps
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) (l k : Fin 3)
    (Mf Ms J eta : ℝ) (hMf : 1 ≤ Mf) (hMs : 1 ≤ Ms) (hJ : 0 ≤ J)
    (hdr : 0 < dr) (hAr : 0 < Ar)
    (hFcap : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i l) x ∧
      |referenceMetricGramFrame g L (q,x) i l| ≤ Mf ∧
      ‖fderiv ℝ (fun y => referenceMetricGramFrame g L (q,y) i l) x‖ ≤ Mf)
    (hScap : ∀ j : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x)| ≤ Ms ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) x‖ ≤ Ms)
    (hBcap : ∀ i j : Fin 3,
      ContDiffAt ℝ ∞ (fun y => data.Bl i j ((Tq dr Ar p q) y)) x ∧
      ‖data.Bl i j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖fderiv ℝ (fun y => data.Bl i j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (hjet' : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    ContDiffAt ℝ ∞ (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k) x ∧
    ‖mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k x‖ ≤
      mixedCoefficientBudget (Mf+Ms) data.M (data.M*data.KT) J*eta/(actualReferenceBeta g L q dr Ar p x) ∧
    ‖fderiv ℝ (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k) x‖ ≤
      mixedCoefficientBudget (Mf+Ms) data.M (data.M*data.KT) J*eta := by
  exact weightedMixedSecondCoefficient_first_caps (E := Half) (F := Neg) (Mf+Ms) data.M (data.M*data.KT) J
    (add_nonneg (zero_le_one.trans hMf) (zero_le_one.trans hMs)) data.M_nonneg (mul_nonneg data.M_nonneg data.KT_pos.le) hJ
    (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => data.Bl i j ((Tq dr Ar p q) y)) x
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
    (fun i => (hFcap i).1) (fun j => (hScap j).1)
    (fun i j => (hBcap i j).1)
    (fun i => by simpa only [Real.norm_eq_abs] using
      ((hFcap i).2.1.trans (le_add_of_nonneg_right (zero_le_one.trans hMs))))
    (fun i => (hFcap i).2.2.trans (le_add_of_nonneg_right (zero_le_one.trans hMs)))
    (fun j => by simpa only [Real.norm_eq_abs] using
      ((hScap j).2.1.trans (le_add_of_nonneg_left (zero_le_one.trans hMf))))
    (fun j => (hScap j).2.2.trans (le_add_of_nonneg_left (zero_le_one.trans hMf)))
    (fun i j => (hBcap i j).2.1) (fun i j => (hBcap i j).2.2)
    (actualReferenceBeta g L q dr Ar p x) eta (referenceRadius_pos dr Ar p L x hdr hAr).le
    hb heta heta1 hs hjet'

set_option diagnostics true in
/-- Fixed-g2 original physical mixed coefficient caps. Uniformity over a metric neighborhood is NOT asserted. -/
theorem exists_mixedAngularSecondCoefficient_uniform_first_caps (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ l k : Fin 3,
        ContDiffAt ℝ ∞ (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
          hreg δ0 W data g2 dr Ar p q l k) x ∧
        ‖mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
          hreg δ0 W data g2 dr Ar p q l k x‖ ≤ Q*eta/(actualReferenceBeta g L q dr Ar p x) ∧
        ‖fderiv ℝ (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
          hreg δ0 W data g2 dr Ar p q l k) x‖ ≤ Q*eta := by
  trace "weighted-factory-entered"
  apply use_scalar_family_cap (exists_metricFrame_uniform_first_caps g hg L y0 ρ)
  intro Mf hMf hFrame
  trace "weighted-frame-selected"
  apply use_scalar_family_cap
    (exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ)
  intro Ms hMs hScalar
  trace "weighted-scalar-selected"
  let Ma := Mf+Ms
  have hMa : 0 ≤ Ma := add_nonneg (zero_le_one.trans hMf) (zero_le_one.trans hMs)
  let jetWitness := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _) 1
  let J : ℝ := Classical.choose jetWitness
  have jetFacts := Classical.choose_spec jetWitness
  have hJ := jetFacts.1
  have hjet := jetFacts.2
  have hB0 : 0 ≤ data.M := data.M_nonneg
  have hB1 : 0 ≤ data.M*data.KT := mul_nonneg data.M_nonneg data.KT_pos.le
  trace "weighted-budget-prepared"
  refine ⟨mixedCoefficientBudget Ma data.M (data.M*data.KT) J,?_,?_⟩
  · unfold mixedCoefficientBudget
    positivity
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs l k
  trace "weighted-point-entered"
  have hFcap (i : Fin 3) := hFrame q hq x hx i l
  have hScap (j : Fin 3) := hScalar q hq x hx dr Ar p k j
  have hBcap (i j : Fin 3) :=
    (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i j).2.2.1
  have hjet' : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x := by
    simpa only [norm_iteratedFDeriv_one,pow_one,actualReferenceBeta,J,jetWitness]
      using (hjet q hq dr hdr hdr1 Ar hAr p hp x hx).1
  trace "weighted-physical-caps-selected"
  apply mixedAngularSecondCoefficient_pointwise_caps hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hreg δ0 W data g2 q dr Ar p x l k Mf Ms J eta hMf hMs hJ.le hdr hAr
  · trace "weighted-apply-frame"
    exact fun i => ⟨(hFcap i).1.contDiffAt,(hFcap i).2⟩
  · trace "weighted-apply-scalar"
    exact fun j => ⟨(hScap j).1.contDiffAt,(hScap j).2⟩
  · trace "weighted-apply-low"
    exact hBcap
  · exact hb
  · exact heta
  · exact heta0.trans data.eta0_le
  · exact hs
  · exact hjet'

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
