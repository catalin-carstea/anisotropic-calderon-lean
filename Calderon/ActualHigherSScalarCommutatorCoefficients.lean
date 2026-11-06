import Calderon.ActualHigherSFirstCoefficientJets
import Calderon.ActualPrincipalErrorCoefficient
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorCoefficients
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation PrincipalCommutator
  ActualScalarPrincipalAdjoint ActualPrincipalErrorCoefficient PerturbedDensityAdjoint
  ActualHigherSFirstCoefficientJets

section Generic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma contDiffAt_directional (f : R3 → V) (x X : R3) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (directionalFDeriv X f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma norm_directional_le (f : R3 → V) (x X : R3) :
    ‖directionalFDeriv X f x‖ ≤ ‖iteratedFDeriv ℝ 1 f x‖*‖X‖ := by
  rw [norm_iteratedFDeriv_one]
  exact ContinuousLinearMap.le_opNorm (fderiv ℝ f x) X

lemma norm_second_directional_le_at (f : R3 → V) (x X Y : R3)
    (hf : ContDiffAt ℝ ∞ f x) :
    ‖directionalFDeriv X (directionalFDeriv Y f) x‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖*‖X‖*‖Y‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : directionalFDeriv X (directionalFDeriv Y f) x =
      fderiv ℝ (fderiv ℝ f) x X Y := by
    unfold directionalFDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const Y)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,fderiv_const_apply,zero_apply,map_zero,add_zero,zero_add]
  have hn : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
  rw [he]
  simpa only [hn] using ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ f) x) X Y

lemma coordinate_jet_caps (f : R3 → V) (x : R3) (K r beta : ℝ)
    (hf : ContDiffAt ℝ ∞ f x)
    (hcap : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n f x‖ ≤ K*r^2*beta^n) :
    ‖f x‖ ≤ K*r^2 ∧
      (∀ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) f x‖ ≤ K*r^2*beta) ∧
      (∀ k m : Fin 3, ‖directionalFDeriv (coordinateDirection m)
        (directionalFDeriv (coordinateDirection k) f) x‖ ≤ K*r^2*beta^2) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hcap 0 (by decide)
  · intro k
    have hn := norm_directional_le f x (coordinateDirection k)
    rw [norm_coordinateDirection,mul_one] at hn
    exact hn.trans (by simpa only [pow_one] using hcap 1 (by decide))
  · intro k m
    have hn := norm_second_directional_le_at f x (coordinateDirection m) (coordinateDirection k) hf
    rw [norm_coordinateDirection,norm_coordinateDirection,mul_one,mul_one] at hn
    exact hn.trans (hcap 2 (by decide))

lemma directional_smul_at (s : R3 → ℝ) (v : R3 → V) (x X : R3)
    (hs : ContDiffAt ℝ ∞ s x) (hv : ContDiffAt ℝ ∞ v x) :
    directionalFDeriv X (fun y => s y • v y) x =
      directionalFDeriv X s x • v x+s x • directionalFDeriv X v x := by
  unfold directionalFDeriv
  rw [fderiv_fun_smul (hs.differentiableAt (by simp)) (hv.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,smul_apply]
  exact add_comm _ _

lemma product_first_jet_budget (s : R3 → ℝ) (v : R3 → V) (x X : R3)
    (hs : ContDiffAt ℝ ∞ s x) (hv : ContDiffAt ℝ ∞ v x)
    (A0 A1 B0 B1 : ℝ) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hs0 : |s x| ≤ A0) (hs1 : |directionalFDeriv X s x| ≤ A1)
    (hv0 : ‖v x‖ ≤ B0) (hv1 : ‖directionalFDeriv X v x‖ ≤ B1) :
    ‖s x • v x‖ ≤ A0*B0 ∧
      ‖directionalFDeriv X (fun y => s y • v y) x‖ ≤ A1*B0+A0*B1 := by
  constructor
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hs0 hv0 (norm_nonneg _) hA0
  · rw [directional_smul_at s v x X hs hv]
    calc
      _ ≤ ‖directionalFDeriv X s x • v x‖+‖s x • directionalFDeriv X v x‖ := norm_add_le _ _
      _ = |directionalFDeriv X s x| *‖v x‖+|s x| *‖directionalFDeriv X v x‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ A1*B0+A0*B1 := add_le_add
        (mul_le_mul hs1 hv0 (norm_nonneg _) hA1)
        (mul_le_mul hs0 hv1 (norm_nonneg _) hA0)

def scalarDerivativeProduct (Z : R3) (a : R3 → ℝ) (b : R3 → V) : R3 → V :=
  fun x => directionalFDeriv Z a x • b x

def operatorDerivativeProduct (Z : R3) (a : R3 → ℝ) (b : R3 → V) : R3 → V :=
  fun x => a x • directionalFDeriv Z b x

def secondOperatorDerivativeProduct (X Y : R3) (a : R3 → ℝ) (b : R3 → V) : R3 → V :=
  fun x => a x • directionalFDeriv X (directionalFDeriv Y b) x

lemma scalarDerivativeProduct_budget (a : R3 → ℝ) (b : R3 → V) (x X Z : R3)
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (A B eps r beta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps) (hbeta : 0 < beta)
    (ha1 : |directionalFDeriv Z a x| ≤ A*eps/beta)
    (ha2 : |directionalFDeriv X (directionalFDeriv Z a) x| ≤ A*eps)
    (hb0 : ‖b x‖ ≤ B*r^2) (hb1 : ‖directionalFDeriv X b x‖ ≤ B*r^2*beta) :
    ‖scalarDerivativeProduct Z a b x‖ ≤ A*B*eps*r^2/beta ∧
      ‖directionalFDeriv X (scalarDerivativeProduct Z a b) x‖ ≤ 2*A*B*eps*r^2 := by
  have h := product_first_jet_budget (directionalFDeriv Z a) b x X
    (contDiffAt_directional a x Z ha) hb (A*eps/beta) (A*eps) (B*r^2) (B*r^2*beta)
    (by positivity) (by positivity) (by positivity) (by positivity) ha1 ha2 hb0 hb1
  constructor
  · calc
      _ ≤ (A*eps/beta)*(B*r^2) := h.1
      _ = _ := by ring
  · calc
      _ ≤ (A*eps)*(B*r^2)+(A*eps/beta)*(B*r^2*beta) := h.2
      _ = _ := by field_simp [hbeta.ne'] <;> ring

lemma operatorDerivativeProduct_budget (a : R3 → ℝ) (b : R3 → V) (x X Z : R3)
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (A B eps r beta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps) (hbeta : 0 < beta)
    (ha0 : |a x| ≤ A*eps/beta^2) (ha1 : |directionalFDeriv X a x| ≤ A*eps/beta)
    (hb1 : ‖directionalFDeriv Z b x‖ ≤ B*r^2*beta)
    (hb2 : ‖directionalFDeriv X (directionalFDeriv Z b) x‖ ≤ B*r^2*beta^2) :
    ‖operatorDerivativeProduct Z a b x‖ ≤ A*B*eps*r^2/beta ∧
      ‖directionalFDeriv X (operatorDerivativeProduct Z a b) x‖ ≤ 2*A*B*eps*r^2 := by
  have h := product_first_jet_budget a (directionalFDeriv Z b) x X
    ha (contDiffAt_directional b x Z hb) (A*eps/beta^2) (A*eps/beta) (B*r^2*beta) (B*r^2*beta^2)
    (by positivity) (by positivity) (by positivity) (by positivity) ha0 ha1 hb1 hb2
  constructor
  · calc
      _ ≤ (A*eps/beta^2)*(B*r^2*beta) := h.1
      _ = _ := by field_simp [hbeta.ne'] <;> ring
  · calc
      _ ≤ (A*eps/beta)*(B*r^2*beta)+(A*eps/beta^2)*(B*r^2*beta^2) := h.2
      _ = _ := by field_simp [hbeta.ne'] <;> ring

lemma secondOperatorDerivativeProduct_budget (a : R3 → ℝ) (b : R3 → V) (x X Y : R3)
    (A B eps r beta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps) (hbeta : 0 < beta)
    (ha0 : |a x| ≤ A*eps/beta^2)
    (hb2 : ‖directionalFDeriv X (directionalFDeriv Y b) x‖ ≤ B*r^2*beta^2) :
    ‖secondOperatorDerivativeProduct X Y a b x‖ ≤ A*B*eps*r^2 := by
  calc
    _ = |a x| *‖directionalFDeriv X (directionalFDeriv Y b) x‖ := by
      rw [secondOperatorDerivativeProduct,norm_smul,Real.norm_eq_abs]
    _ ≤ (A*eps/beta^2)*(B*r^2*beta^2) := mul_le_mul ha0 hb2 (norm_nonneg _) (by positivity)
    _ = _ := by field_simp [hbeta.ne'] <;> ring
end Generic

section CoordinateBudget
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- The distinct second-base row factors and the first-base factor after the genuine cancellation. -/
def CoordinateCommutatorCoefficientBudget
    (a : Fin 3 → Fin 3 → R3 → ℝ) (b : Fin 3 → R3 → V)
    (x : R3) (eps r beta C : ℝ) : Prop :=
  ∀ i j l k m : Fin 3,
    ‖scalarDerivativeProduct (coordinateDirection l) (a i j) (b l) x‖ ≤ C*eps*r^2/beta ∧
    ‖directionalFDeriv (coordinateDirection m)
      (scalarDerivativeProduct (coordinateDirection l) (a i j) (b l)) x‖ ≤ C*eps*r^2 ∧
    ‖operatorDerivativeProduct (coordinateDirection k) (a i j) (b l) x‖ ≤ C*eps*r^2/beta ∧
    ‖directionalFDeriv (coordinateDirection m)
      (operatorDerivativeProduct (coordinateDirection k) (a i j) (b l)) x‖ ≤ C*eps*r^2 ∧
    ‖secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j)
      (a i j) (b l) x‖ ≤ C*eps*r^2

lemma coordinateCommutatorCoefficientBudget_of_bounds
    (a : Fin 3 → Fin 3 → R3 → ℝ) (b : Fin 3 → R3 → V)
    (x : R3) (eps r beta A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 ≤ eps) (hbeta : 0 < beta)
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ l, ContDiffAt ℝ ∞ (b l) x)
    (ha0 : ∀ i j, |a i j x| ≤ A*eps/beta^2)
    (ha1 : ∀ i j k, |directionalFDeriv (coordinateDirection k) (a i j) x| ≤ A*eps/beta)
    (ha2 : ∀ i j k m, |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (a i j)) x| ≤ A*eps)
    (hb0 : ∀ l, ‖b l x‖ ≤ B*r^2)
    (hb1 : ∀ l k, ‖directionalFDeriv (coordinateDirection k) (b l) x‖ ≤ B*r^2*beta)
    (hb2 : ∀ l k m, ‖directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (b l)) x‖ ≤ B*r^2*beta^2) :
    CoordinateCommutatorCoefficientBudget a b x eps r beta (2*A*B) := by
  have hup0 (z : ℝ) (hz : z ≤ A*B*eps*r^2/beta) : z ≤ (2*A*B)*eps*r^2/beta := by
    have h0 : 0 ≤ A*B*eps*r^2/beta := by positivity
    exact hz.trans (by
      have he : (2*A*B)*eps*r^2/beta = 2*(A*B*eps*r^2/beta) := by ring
      rw [he]; linarith)
  have hup1 (z : ℝ) (hz : z ≤ A*B*eps*r^2) : z ≤ (2*A*B)*eps*r^2 := by
    have h0 : 0 ≤ A*B*eps*r^2 := by positivity
    exact hz.trans (by nlinarith)
  intro i j l k m
  have h0 := scalarDerivativeProduct_budget (a i j) (b l) x (coordinateDirection m)
    (coordinateDirection l) (ha i j) (hb l) A B eps r beta hA hB heps hbeta
    (ha1 i j l) (ha2 i j l m) (hb0 l) (hb1 l m)
  have h1 := operatorDerivativeProduct_budget (a i j) (b l) x (coordinateDirection m)
    (coordinateDirection k) (ha i j) (hb l) A B eps r beta hA hB heps hbeta
    (ha0 i j) (ha1 i j m) (hb1 l k) (hb2 l k m)
  have h2 := secondOperatorDerivativeProduct_budget (a i j) (b l) x (coordinateDirection i)
    (coordinateDirection j) A B eps r beta hA hB heps hbeta (ha0 i j) (hb2 l j i)
  refine ⟨hup0 _ h0.1,?_,hup0 _ h1.1,?_,hup1 _ h2⟩
  · simpa only [mul_assoc] using h0.2
  · simpa only [mul_assoc] using h1.2
end CoordinateBudget

private structure PrincipalTwoJetData (g : MatrixField) (L : ℝ) (K : Set R3) where
  A : ℝ
  pos : 0 < A
  cap : ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ x ∈ K,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ eps →
    ∀ i j k l : Fin 3,
      |actualPrincipalMatrix g L q δr Ar p h x i j| ≤ A*eps/(actualReferenceBeta g L q δr Ar p x)^2 ∧
      |directionalFDeriv (coordinateDirection k)
        (fun y => actualPrincipalMatrix g L q δr Ar p h y i j) x| ≤ A*eps/actualReferenceBeta g L q δr Ar p x ∧
      |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
        (fun y => actualPrincipalMatrix g L q δr Ar p h y i j)) x| ≤ A*eps

private theorem exists_principalTwoJetData (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    Nonempty (PrincipalTwoJetData g L K) := by
  obtain ⟨A0,A1,A2,hA0,hA1,hA2,hcap⟩ :=
    exists_actual_principal_uniform_two_jet_bound g hg L hL K hK
  let A : ℝ := 1+A0+A1+A2
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 : A0 ≤ A := by dsimp [A]; linarith
  have h1 : A1 ≤ A := by dsimp [A]; linarith
  have h2 : A2 ≤ A := by dsimp [A]; linarith
  refine ⟨⟨A,hA,?_⟩⟩
  intro q hq δr Ar p hδr hδr1 hAr hp x hx eps heps heps1 h hh hjet hb hsmall i j k l
  have hc := hcap q hq δr hδr hδr1 Ar hAr p hp x hx eps heps heps1 h hh hjet hb hsmall i j k l
  have hBeta : actualReferenceBeta g L q δr Ar p x =
      metricDifferentialNorm (referenceMetric (dilatedMetric g q) L)
        (fun y => Real.log (referenceRadius δr Ar p L y)) x := by
    unfold actualReferenceBeta
    rfl
  rw [← hBeta] at hc
  have hbpos : 0 < actualReferenceBeta g L q δr Ar p x := lt_of_lt_of_le zero_lt_one hb
  refine ⟨?_,?_,?_⟩
  · change |actualPrincipalMatrix g L q δr Ar p h x i j| ≤ _
    apply hc.1.trans
    gcongr
  · apply hc.2.1.trans
    gcongr
  · exact hc.2.2.trans (mul_le_mul_of_nonneg_right h2 heps)

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def coeffLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] coeffLowNormed
@[instance_reducible] private def coeffLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] coeffLowModule

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BCC" => canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private structure FirstCoefficientJetData (δ : ℝ) (g2 : MatrixField) where
  K : ℝ
  pos : 0 < K
  cap : ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
    ∀ l : Fin 3, ∀ n : ℕ, n ≤ 2 →
    ‖iteratedFDeriv ℝ n (fun y => BCC g2 δr Ar p q y l) x‖ ≤
      K*(referenceRadius δr Ar p L x)^2*(actualReferenceBeta g L q δr Ar p x)^n
local notation "FirstData" => FirstCoefficientJetData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private theorem exists_firstCoefficientJetData (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Nonempty (FirstData δ g2) := by
  obtain ⟨K,hK,hcap⟩ := exists_canonicalFirstCoordinateCoefficient_uniform_two_jet_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  exact ⟨⟨K,hK,hcap⟩⟩

attribute [local irreducible] canonicalFirstCoordinateCoefficient actualPrincipalMatrix
  actualReferenceBeta referenceRadius

/-- Exact actual surviving-coefficient task; all profile and principal-perturbation hypotheses are explicit. -/
def ActualCoefficientBudget (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ Kc : ℝ, 0 < Kc ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
    (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ eps →
    CoordinateCommutatorCoefficientBudget
      (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
      (fun l y => BCC g2 δr Ar p q y l) x eps (referenceRadius δr Ar p L x)
      (actualReferenceBeta g L q δr Ar p x) Kc
local notation "ActualBudget" => ActualCoefficientBudget g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private theorem actualCoefficientBudget_of_data (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (D : PrincipalTwoJetData g L (closedBall y0 ρ)) (Fj : FirstData δ g2) :
    ActualBudget δ g2 := by
  have hA : 0 < D.A := D.pos
  have hB : 0 < Fj.K := Fj.pos
  refine ⟨2*D.A*Fj.K,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh x hx hjet hb hsmall
  let r : ℝ := referenceRadius δr Ar p L x
  let beta : ℝ := actualReferenceBeta g L q δr Ar p x
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let bb : Fin 3 → R3 → (Half →L[ℝ] Neg) := fun l y => BCC g2 δr Ar p q y l
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hxK : x ∈ closedBall y0 ρ := by
    simpa only [ActualHigherSFormation.higherSParam] using hx.1.2.1
  have has := D.cap q hq δr Ar p hδr hδr1 hAr hp x hxK eps heps heps1 h hh hjet hb hsmall
  have hbs := Fj.cap δr Ar p hδr hδr1 hAr hp q hq x hx hb (hsmall.trans heps1)
  have ha (i j : Fin 3) : ContDiffAt ℝ ∞ (aa i j) x :=
    (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh i j).contDiffAt
  have hbg (l : Fin 3) : ContDiffAt ℝ ∞ (bb l) x :=
    contDiffAt_canonicalFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q x hx l
  have ha0 (i j : Fin 3) : |aa i j x| ≤ D.A*eps/beta^2 := (has i j 0 0).1
  have ha1 (i j k : Fin 3) : |directionalFDeriv (coordinateDirection k) (aa i j) x| ≤
      D.A*eps/beta := (has i j k 0).2.1
  have ha2 (i j k m : Fin 3) : |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (aa i j)) x| ≤ D.A*eps := (has i j k m).2.2
  have hbcaps (l : Fin 3) := coordinate_jet_caps (bb l) x Fj.K r beta (hbg l) (hbs l)
  have hb0 (l : Fin 3) : ‖bb l x‖ ≤ Fj.K*r^2 := (hbcaps l).1
  have hb1 (l k : Fin 3) : ‖directionalFDeriv (coordinateDirection k) (bb l) x‖ ≤
      Fj.K*r^2*beta := (hbcaps l).2.1 k
  have hb2 (l k m : Fin 3) : ‖directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (bb l)) x‖ ≤ Fj.K*r^2*beta^2 := (hbcaps l).2.2 k m
  exact coordinateCommutatorCoefficientBudget_of_bounds aa bb x eps r beta D.A Fj.K
    D.pos.le Fj.pos.le heps hbpos ha hbg ha0 ha1 ha2 hb0 hb1 hb2

/-- Uniform actual coefficient budgets before profiles and angular input size. -/
theorem exists_actual_scalar_first_coordinate_commutator_coefficient_bounds
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : ActualBudget δ g2 := by
  have hK : IsCompact (closedBall y0 ρ) := isCompact_closedBall y0 ρ
  obtain ⟨D⟩ := exists_principalTwoJetData g hg L hL (closedBall y0 ρ) hK
  obtain ⟨Fj⟩ := exists_firstCoefficientJetData g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  exact actualCoefficientBudget_of_data g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 D Fj

/-- Retain the same W; room and Jacobian witnesses precede g2 and every profile. -/
theorem exists_retained_actual_scalar_first_coordinate_commutator_coefficient_bounds
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ActualBudget δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_first_coordinate_commutator_coefficient_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorCoefficients
