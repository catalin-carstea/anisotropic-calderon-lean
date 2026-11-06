/- Actual uniform O(r) zero-base HigherS coefficient bound. -/
import Calderon.ActualHigherSCoefficientBounds
import Calderon.ActualReferenceProfileParameterJets
import Calderon.FixedProfileBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/- Cached standard instances only: each body is the pre-existing inferred
canonical instance; no norm convention or bound is replaced. -/
@[instance_reducible] private def zeroCoeffInnerNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def zeroCoeffInnerModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def zeroCoeffParameterNormed :
    NormedAddCommGroup ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def zeroCoeffParameterModule :
    NormedSpace ℝ ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) := inferInstance
attribute [local instance] zeroCoeffInnerNormed zeroCoeffInnerModule
  zeroCoeffParameterNormed zeroCoeffParameterModule

/-! ## 1. Generic typed norm algebra (no Sobolev bodies) -/

private lemma norm_sum_three_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin 3 → ℝ) (v : Fin 3 → E) (A V : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i, |a i| ≤ A) (hv : ∀ i, ‖v i‖ ≤ V) :
    ‖∑ i : Fin 3, a i • v i‖ ≤ 3*A*V := by
  calc
    _ ≤ ∑ i : Fin 3, ‖a i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, A*V := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (ha i) (hv i) (norm_nonneg _) hA
    _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma norm_double_sum_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → Fin 3 → E) (A V : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i j, |a i j| ≤ A) (hv : ∀ i j, ‖v i j‖ ≤ V) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, a i j • v i j‖ ≤ 9*A*V := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, a i j • v i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 3*A*V := Finset.sum_le_sum (fun i _ =>
      norm_sum_three_smul_le (a i) (v i) A V hA (ha i) (hv i))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

/-- Norm of the angular-map shape `½ Σ_ab c_ab T_ab`. -/
private lemma norm_half_double_sum_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : Fin 3 → Fin 3 → ℝ) (T : Fin 3 → Fin 3 → E →L[ℝ] F) (A V : ℝ) (hA : 0 ≤ A)
    (hc : ∀ a b, |c a b| ≤ A) (hT : ∀ a b, ‖T a b‖ ≤ V) :
    ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤ 9*A*V := by
  have h := norm_double_sum_smul_le c T A V hA hc hT
  have hh : ‖(1/2 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> norm_num
  rw [norm_smul]
  calc
    ‖(1/2 : ℝ)‖ * ‖∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤ 1*(9*A*V) :=
      mul_le_mul hh h (norm_nonneg _) zero_le_one
    _ = 9*A*V := one_mul _

private lemma norm_le_sum_norm {E : Type*} [SeminormedAddCommGroup E] (f : Fin 3 → E) (j : Fin 3) :
    ‖f j‖ ≤ ∑ k : Fin 3, ‖f k‖ :=
  Finset.single_le_sum (f := fun k : Fin 3 => ‖f k‖) (fun k _ => norm_nonneg _) (Finset.mem_univ j)

private lemma norm_le_double_sum_norm {E : Type*} [SeminormedAddCommGroup E]
    (f : Fin 3 → Fin 3 → E) (a b : Fin 3) :
    ‖f a b‖ ≤ ∑ a' : Fin 3, ∑ b' : Fin 3, ‖f a' b'‖ :=
  (norm_le_sum_norm (f a) b).trans
    (Finset.single_le_sum (f := fun a' : Fin 3 => ∑ b' : Fin 3, ‖f a' b'‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ a))

/-- Lemma A: the exact Second-row shape, `‖Z‖ ≤ 9 M³ β`. -/
lemma norm_row_shape_le {E1 E2 E3 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [NormedAddCommGroup E3] [NormedSpace ℝ E3]
    (J : E2 →L[ℝ] E3) (D : E1 →L[ℝ] E2) (Olo Blo El : E2 →L[ℝ] E3) (Ohi Bhi Eh : E1 →L[ℝ] E2)
    (Ek : Fin 3 → E1 →L[ℝ] E2) (fi fj : ℝ) (Γ : Fin 3 → ℝ) (M β : ℝ) (hM : 1 ≤ M) (hβ : 1 ≤ β)
    (hJ : ‖J‖ ≤ M) (hD : ‖D‖ ≤ M) (hOlo : ‖Olo‖ ≤ M) (hBlo : ‖Blo‖ ≤ M) (hEl : ‖El‖ ≤ M)
    (hOhi : ‖Ohi‖ ≤ M) (hBhi : ‖Bhi‖ ≤ M) (hEh : ‖Eh‖ ≤ M) (hEk : ∀ k, ‖Ek k‖ ≤ M)
    (hfi : |fi| ≤ M*β) (hfj : |fj| ≤ M*β) (hΓ : ∀ k, |Γ k| ≤ M) :
    ‖J.comp D + (Olo + fi • Blo).comp Eh + El.comp (Ohi + fj • Bhi) + fi • J.comp Eh -
      ∑ k : Fin 3, Γ k • J.comp (Ek k)‖ ≤ 9*M^3*β := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hβ0 : 0 ≤ β := le_trans zero_le_one hβ
  have hMb : 0 ≤ M*β := mul_nonneg hM0 hβ0
  have hfi' : ‖fi • Blo‖ ≤ M*β*M := by
    rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hfi hBlo (norm_nonneg _) hMb
  have hfj' : ‖fj • Bhi‖ ≤ M*β*M := by
    rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hfj hBhi (norm_nonneg _) hMb
  have hJE : ‖J.comp Eh‖ ≤ M*M :=
    (ContinuousLinearMap.opNorm_comp_le J Eh).trans (mul_le_mul hJ hEh (norm_nonneg _) hM0)
  have h1 : ‖J.comp D‖ ≤ M*M :=
    (ContinuousLinearMap.opNorm_comp_le J D).trans (mul_le_mul hJ hD (norm_nonneg _) hM0)
  have h2 : ‖(Olo + fi • Blo).comp Eh‖ ≤ (M + M*β*M)*M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
      ((norm_add_le _ _).trans (add_le_add hOlo hfi')) hEh (norm_nonneg _) (by positivity))
  have h3 : ‖El.comp (Ohi + fj • Bhi)‖ ≤ M*(M + M*β*M) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hEl
      ((norm_add_le _ _).trans (add_le_add hOhi hfj')) (norm_nonneg _) hM0)
  have h4 : ‖fi • J.comp Eh‖ ≤ M*β*(M*M) := by
    rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul hfi hJE (norm_nonneg _) hMb
  have h5 : ‖∑ k : Fin 3, Γ k • J.comp (Ek k)‖ ≤ 3*M*(M*M) :=
    norm_sum_three_smul_le Γ (fun k => J.comp (Ek k)) M (M*M) hM0 hΓ
      (fun k => (ContinuousLinearMap.opNorm_comp_le J (Ek k)).trans
        (mul_le_mul hJ (hEk k) (norm_nonneg _) hM0))
  have a1 := norm_add_le (J.comp D + (Olo + fi • Blo).comp Eh + El.comp (Ohi + fj • Bhi))
    (fi • J.comp Eh)
  have a2 := norm_add_le (J.comp D + (Olo + fi • Blo).comp Eh) (El.comp (Ohi + fj • Bhi))
  have a3 := norm_add_le (J.comp D) ((Olo + fi • Blo).comp Eh)
  have a4 := norm_sub_le (J.comp D + (Olo + fi • Blo).comp Eh + El.comp (Ohi + fj • Bhi) +
    fi • J.comp Eh) (∑ k : Fin 3, Γ k • J.comp (Ek k))
  have hMM : M*M ≤ M^3*β := by
    have h1M : 1 ≤ M*β := one_le_mul_of_one_le_of_one_le hM hβ
    calc
      M*M = M*M*1 := (mul_one _).symm
      _ ≤ M*M*(M*β) := mul_le_mul_of_nonneg_left h1M (mul_nonneg hM0 hM0)
      _ = M^3*β := by ring
  have hM3 : M^3 ≤ M^3*β := le_mul_of_one_le_right (pow_nonneg hM0 3) hβ
  nlinarith [h1,h2,h3,h4,h5,a1,a2,a3,a4,hMM,hM3]

private lemma norm_four_terms_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr0 : 0 ≤ r) (S1 S2 S3 S4 : E) (a1 a2 a3 a4 : ℝ)
    (h1 : ‖S1‖ ≤ a1) (h2 : ‖S2‖ ≤ a2) (h3 : ‖S3‖ ≤ a3) (h4 : ‖S4‖ ≤ a4) :
    ‖(r^2 • S1 + r^2 • S2) + r • S3 + r^3 • S4‖ ≤ r^2*a1 + r^2*a2 + r*a3 + r^3*a4 := by
  have hr2 : 0 ≤ r^2 := pow_nonneg hr0 2
  have hr3 : 0 ≤ r^3 := pow_nonneg hr0 3
  have e1 : ‖r^2 • S1‖ ≤ r^2*a1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr2]; exact mul_le_mul_of_nonneg_left h1 hr2
  have e2 : ‖r^2 • S2‖ ≤ r^2*a2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr2]; exact mul_le_mul_of_nonneg_left h2 hr2
  have e3 : ‖r • S3‖ ≤ r*a3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]; exact mul_le_mul_of_nonneg_left h3 hr0
  have e4 : ‖r^3 • S4‖ ≤ r^3*a4 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr3]; exact mul_le_mul_of_nonneg_left h4 hr3
  have b1 := norm_add_le (r^2 • S1 + r^2 • S2 + r • S3) (r^3 • S4)
  have b2 := norm_add_le (r^2 • S1 + r^2 • S2) (r • S3)
  have b3 := norm_add_le (r^2 • S1) (r^2 • S2)
  linarith

/-- Lemma B: complete zero-base coefficient, `‖CZ‖ ≤ 111 M⁴ r`, all four original
groups retained in order, no symmetry of `Q`. -/
lemma norm_zeroCoefficient_le (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (M β : ℝ) (hM : 1 ≤ M) (hβ : 1 ≤ β) (hr0 : 0 ≤ r) (hrβ : r*β^2 ≤ 1)
    (hJ : ‖JL‖ ≤ M) (hQ : ∀ i j, |Q i j| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (hZ : ∀ i j, ‖Z i j‖ ≤ 9*M^3*β) (hEh : ∀ j, ‖Eh j‖ ≤ M) (hEl : ∀ i, ‖El i‖ ≤ M)
    (hAlo : ∀ i, ‖Alo i‖ ≤ M) (hAhi : ∀ j, ‖Ahi j‖ ≤ M) :
    ‖ActualHigherSCoefficientExtraction.zeroCoefficient r Q b Z Eh El Alo Ahi‖ ≤ 111*M^4*r := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hbb : β ≤ β^2 := by nlinarith
  have hrb : r*β ≤ 1 := (mul_le_mul_of_nonneg_left hbb hr0).trans hrβ
  have hr1 : r ≤ 1 := (le_mul_of_one_le_right hr0 hβ).trans hrb
  have h1 := norm_double_sum_smul_le Q Z M (9*M^3*β) hM0 hQ hZ
  have h2 := norm_sum_three_smul_le b (fun i => (JL).comp (Eh i)) M (M*M) hM0 hb
    (fun i => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hJ (hEh i) (norm_nonneg _) hM0))
  have h3 := norm_double_sum_smul_le Q (fun i j => (Alo i).comp (Eh j) + (El i).comp (Ahi j))
    M (M*M+M*M) hM0 hQ
    (fun i j => (norm_add_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hAlo i) (hEh j) (norm_nonneg _) hM0))
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hEl i) (hAhi j) (norm_nonneg _) hM0))))
  have h4 := norm_double_sum_smul_le Q (fun i j => (El i).comp (Eh j)) M (M*M) hM0 hQ
    (fun i j => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hEl i) (hEh j) (norm_nonneg _) hM0))
  have hz : ‖ActualHigherSCoefficientExtraction.zeroCoefficient r Q b Z Eh El Alo Ahi‖ ≤
      r^2*(9*M*(9*M^3*β)) + r^2*(3*M*(M*M)) + r*(9*M*(M*M+M*M)) + r^3*(9*M*(M*M)) :=
    norm_four_terms_le r hr0
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j)
      (∑ i : Fin 3, b i • (JL).comp (Eh i))
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((Alo i).comp (Eh j)+(El i).comp (Ahi j)))
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El i).comp (Eh j)) _ _ _ _ h1 h2 h3 h4
  have r2β : r^2*β ≤ r := by
    calc
      r^2*β = r*(r*β) := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left hrb hr0
      _ = r := mul_one r
  have r2 : r^2 ≤ r := by
    calc
      r^2 = r*r := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left hr1 hr0
      _ = r := mul_one r
  have r3 : r^3 ≤ r := by
    calc
      r^3 = r*r^2 := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left (r2.trans hr1) hr0
      _ = r := mul_one r
  have hM4 : 0 ≤ M^4 := pow_nonneg hM0 4
  have hM3 : 0 ≤ M^3 := pow_nonneg hM0 3
  have k1 : M^4*(r^2*β) ≤ M^4*r := mul_le_mul_of_nonneg_left r2β hM4
  have k2 : M^3*r^2 ≤ M^3*r := mul_le_mul_of_nonneg_left r2 hM3
  have k3 : M^3*r^3 ≤ M^3*r := mul_le_mul_of_nonneg_left r3 hM3
  have m34 : M^3 ≤ M^4 := by
    calc
      M^3 ≤ M^3*M := le_mul_of_one_le_right hM3 hM
      _ = M^4 := by ring
  have k4 : M^3*r ≤ M^4*r := mul_le_mul_of_nonneg_right m34 hr0
  calc
    _ ≤ _ := hz
    _ ≤ 111*M^4*r := by nlinarith [k1,k2,k3,k4]

/-- Typed chain-rule norm calculation, without expanding concrete coefficient bodies. -/
private lemma norm_fderiv_comp_apply_le {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : F → V) (t : E → F) (x : E) (v : E) (A B D : ℝ)
    (hf : DifferentiableAt ℝ f (t x)) (ht : DifferentiableAt ℝ t x)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdf : ‖fderiv ℝ f (t x)‖ ≤ A) (hdt : ‖fderiv ℝ t x‖ ≤ B)
    (hv : ‖v‖ ≤ D) : ‖fderiv ℝ (f ∘ t) x v‖ ≤ (A*B)*D := by
  rw [fderiv_comp x hf ht]
  have hop : ‖(fderiv ℝ f (t x)).comp (fderiv ℝ t x)‖ ≤ A*B :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hdf hdt (norm_nonneg _) hA)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hop hv (norm_nonneg _) (mul_nonneg hA hB))

/-- Family bound on a compact set (local copy of the private helper in
`ActualHigherSCoefficientBounds`). -/
private lemma compact_family_bound {α E ι : Type*} [TopologicalSpace α]
    [SeminormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : ι, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : ι => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : ι, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : ι, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : ι, |C j| := Finset.single_le_sum (f := fun j : ι => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : ι, |C j| := by linarith

/-! ## 2. Actual geometry -/

section Actual
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => ActualHigherSCoefficientExtraction.profileLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow sphereSobolevInclusionL
 referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
 referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint

/-- Exact frame convention: the actual conformal-frame operator sends `e_i` to `X_i`. -/
lemma conformalFrame_coordinateVector_eq (q : ℝ) (y : R3) (i : Fin 3) :
    conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) =
      referenceMetricGramFrame g L (q,y) i := by
  rw [conformalReferenceGramFrameOperatorJoint_eq_frameOperator,frameOperator_coordinateVector,
    conformalReferenceGramFrame_eq_referenceMetricGramFrame]

/-- Retained-data intermediate: ONE `K` for fixed admissible `g2`, chosen before
`δr,Ar,p,q,x`; every zero-base term (derivative, connection, angular, drift,
quadratic) is bounded by `K·R(x)`. -/
theorem exists_actual_zero_coefficient_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x * (actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      ‖CZ g2 δr Ar p q x‖ ≤ K * referenceRadius δr Ar p L x := by
  classical
  -- (1) compact sets, all fixed before every profile
  have hKx : IsCompact (closedBall y0 ρ) := isCompact_closedBall y0 ρ
  have hKP : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hKQ : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) := isCompact_Icc.prod hKx
  -- (2) existing parameter-jet cap
  have hJetFull := exists_reference_radius_parameter_uniform_jet_bounds g hg L hL
    (closedBall y0 ρ) hKx
  rcases hJetFull with ⟨CT,hCT0,hCT⟩
  -- (3) existing log-radius first jet
  have hLogFull := exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg
    (closedBall y0 ρ) hKx L hL
  rcases hLogFull with ⟨J1,J2,hJ10,_hJ20,hJ1⟩
  -- (4) existing horizontal geometry: connection coefficients
  have hGeoFull := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds g hg L
    (closedBall y0 ρ) hKx
  rcases hGeoFull with ⟨MG,hMG,hGeo⟩
  -- (5) existing EL bound
  have hELFull := ActualHigherSCoefficientBounds.exists_canonicalLow_uniform_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  rcases hELFull with ⟨CE,hCE,hELc⟩
  -- (6) EH and dEH from the ambient germs
  have hEHFull := compact_family_bound (ParamRoom δ) hKP (fun j : Fin 3 => EH j)
    (fun j t ht => (Cm.germHigh j t ht).continuousAt.continuousWithinAt)
  rcases hEHFull with ⟨CH,hCH,hEHc⟩
  have hdEHFull := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun j : Fin 3 => EH j) (ParamRoom δ) hKP
    (fun j t ht => Cm.germHigh j t ht) 1
  rcases hdEHFull with ⟨CH1raw,hCH1raw,hdEHraw⟩
  let CH1 := 1+CH1raw
  have hCH1 : 1 ≤ CH1 := by dsimp [CH1]; linarith
  have hdEHc (j : Fin 3) (t) (ht : t ∈ ParamRoom δ) : ‖fderiv ℝ (EH j) t‖ ≤ CH1 := by
    have h := hdEHraw 1 (le_refl _) t ht j
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (by dsimp [CH1]; linarith)
  -- (7) frame vectors
  have hXFull := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) hKQ
    (fun i : Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  rcases hXFull with ⟨CX,hCX,hXc⟩
  -- (8) after g2: drift and principal coefficients
  have hbFull := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) hKQ
    (fun i : Fin 3 => fun t : ℝ × R3 => normalizedSecondDriftFrameJoint g g2 L i t)
    (fun i => (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.continuousOn)
  rcases hbFull with ⟨Cb,hCb,hbc⟩
  have hQFull := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    g L y0 ρ hg g2 hg2
  rcases hQFull with ⟨CQ,hCQ,hQc⟩
  -- (9) fixed bounded operators
  let Ahi : Fin 3 → Hi →L[ℝ] Half := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
  let Alo : Fin 3 → Half →L[ℝ] Neg := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)
  let NC : ℝ := ‖(JL : Half →L[ℝ] Neg)‖ +
    ‖(sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)‖ +
    ‖(sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)‖ +
    ∑ j : Fin 3, ‖Ahi j‖ + ∑ j : Fin 3, ‖Alo j‖ +
    ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (3/2 : ℝ) a' b'‖ +
    ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (1/2 : ℝ) a' b'‖
  have nJ0 := norm_nonneg (JL : Half →L[ℝ] Neg)
  have nBh0 := norm_nonneg (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
  have nBl0 := norm_nonneg (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
  have nAh0 : 0 ≤ ∑ j : Fin 3, ‖Ahi j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (Ahi j))
  have nAl0 : 0 ≤ ∑ j : Fin 3, ‖Alo j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (Alo j))
  have nRh0 : 0 ≤ ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (3/2 : ℝ) a' b'‖ :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg (sphereSobolevRotationL (3/2 : ℝ) a b)))
  have nRl0 : 0 ≤ ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (1/2 : ℝ) a' b'‖ :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg (sphereSobolevRotationL (1/2 : ℝ) a b)))
  have hNC0 : 0 ≤ NC := by dsimp only [NC]; linarith
  have hJN : ‖(JL : Half →L[ℝ] Neg)‖ ≤ NC := by dsimp only [NC]; linarith
  have hBhN : ‖(sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)‖ ≤ NC := by
    dsimp only [NC]; linarith
  have hBlN : ‖(sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)‖ ≤ NC := by
    dsimp only [NC]; linarith
  have hAhN (j : Fin 3) : ‖Ahi j‖ ≤ NC := by
    have := norm_le_sum_norm Ahi j; dsimp only [NC]; linarith
  have hAlN (j : Fin 3) : ‖Alo j‖ ≤ NC := by
    have := norm_le_sum_norm Alo j; dsimp only [NC]; linarith
  have hRhN (a' b' : Fin 3) : ‖sphereSobolevRotationL (3/2 : ℝ) a' b'‖ ≤ NC := by
    have := norm_le_double_sum_norm (fun a b => sphereSobolevRotationL (3/2 : ℝ) a b) a' b'
    dsimp only [NC]; linarith
  have hRlN (a' b' : Fin 3) : ‖sphereSobolevRotationL (1/2 : ℝ) a' b'‖ ≤ NC := by
    have := norm_le_double_sum_norm (fun a b => sphereSobolevRotationL (1/2 : ℝ) a b) a' b'
    dsimp only [NC]; linarith
  -- (10) the single dominating constant, fixed before every profile
  have hMG0 : 0 ≤ MG := le_trans zero_le_one hMG
  have hCT0' : 0 ≤ CT := le_of_lt hCT0
  have hJ10' : 0 ≤ J1 := le_of_lt hJ10
  have hCX0 : 0 ≤ CX := le_trans zero_le_one hCX
  have hCH10 : 0 ≤ CH1 := le_trans zero_le_one hCH1
  have hp1 : 0 ≤ 9*MG*NC := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hMG0) hNC0
  have hp2 : 0 ≤ CH1*CT*CX := mul_nonneg (mul_nonneg hCH10 hCT0') hCX0
  have hp3 : 0 ≤ J1*CX := mul_nonneg hJ10' hCX0
  let M : ℝ := 1 + CQ + Cb + CH + CE + NC + 9*MG*NC + MG + CH1*CT*CX + J1*CX
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hQM : CQ ≤ M := by dsimp only [M]; linarith
  have hbM : Cb ≤ M := by dsimp only [M]; linarith
  have hHM : CH ≤ M := by dsimp only [M]; linarith
  have hEM : CE ≤ M := by dsimp only [M]; linarith
  have hNM : NC ≤ M := by dsimp only [M]; linarith
  have hOM : 9*MG*NC ≤ M := by dsimp only [M]; linarith
  have hGM : MG ≤ M := by dsimp only [M]; linarith
  have hDM : CH1*CT*CX ≤ M := by dsimp only [M]; linarith
  have hfM : J1*CX ≤ M := by dsimp only [M]; linarith
  refine ⟨111*M^4,mul_nonneg (by norm_num : (0 : ℝ) ≤ 111) (pow_nonneg hM0 4),?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ hsmall
  -- profile data
  have hxK : x ∈ closedBall y0 ρ := hx.1.2.1
  have hqx : (q,x) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ := ⟨hq,hxK⟩
  have hr0 : 0 ≤ referenceRadius δr Ar p L x := le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hβ0 : 0 ≤ actualReferenceBeta g L q δr Ar p x := le_trans zero_le_one hβ
  have hdR : ‖fderiv ℝ (referenceRadius δr Ar p L) x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.2
  -- parameter jet: ‖d t_R(x)‖ ≤ CT
  have hjet := hCT q hq δr hδr hδr1 Ar hAr p hp x hxK hβ hsmall hdR
  have hjet1 : ‖iteratedFDeriv ℝ 1 (Tq δr Ar p q) x‖ ≤ CT := hjet.2.1
  have hT1 : ‖fderiv ℝ (Tq δr Ar p q) x‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one]; exact hjet1
  have hTc := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q
  have hTd : DifferentiableAt ℝ (Tq δr Ar p q) x := hTc.differentiable (by simp) x
  -- geometry at (q,x)
  have hG := hGeo q hq x hxK
  have hΓ (i k j : Fin 3) : |referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j| ≤ M := (hG.2.2.2 i k j).trans hGM
  have hXn (i : Fin 3) : ‖referenceMetricGramFrame g L (q,x) i‖ ≤ CX := hXc i (q,x) hqx
  have hOhi (i : Fin 3) : ‖referenceHighHorizontalAngularL g L q x i‖ ≤ M := by
    have h : ‖referenceHighHorizontalAngularL g L q x i‖ ≤ 9*MG*NC := by
      unfold referenceHighHorizontalAngularL
      exact norm_half_double_sum_le
        (fun a' b' => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a' b')
        (fun a' b' => sphereSobolevRotationL (3/2 : ℝ) a' b') MG NC hMG0
        (fun a' b' => hG.2.2.2 i a' b') hRhN
    exact h.trans hOM
  have hOlo (i : Fin 3) : ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ M := by
    have h : ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ 9*MG*NC := by
      unfold referenceLowerHorizontalAngularL
      exact norm_half_double_sum_le
        (fun a' b' => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a' b')
        (fun a' b' => sphereSobolevRotationL (1/2 : ℝ) a' b') MG NC hMG0
        (fun a' b' => hG.2.2.2 i a' b') hRlN
    exact h.trans hOM
  -- frame log derivative: |f_i| ≤ J1·CX·β ≤ M β
  have hlog : ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖ ≤
      J1 * actualReferenceBeta g L q δr Ar p x :=
    (hJ1 q hq δr hδr hδr1 Ar hAr p hp x hxK).1
  have hf (k : Fin 3) : |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x k| ≤
      M * actualReferenceBeta g L q δr Ar p x := by
    have he : referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x k =
        fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x
          (referenceMetricGramFrame g L (q,x) k) := by
      unfold referenceRadiusHorizontalLogDerivative
      rw [conformalFrame_coordinateVector_eq g L q x k]
    rw [he,← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖ *
          ‖referenceMetricGramFrame g L (q,x) k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (J1 * actualReferenceBeta g L q δr Ar p x) * CX :=
        mul_le_mul hlog (hXn k) (norm_nonneg _) (mul_nonneg hJ10' hβ0)
      _ = (J1*CX) * actualReferenceBeta g L q δr Ar p x := by ring
      _ ≤ M * actualReferenceBeta g L q δr Ar p x := mul_le_mul_of_nonneg_right hfM hβ0
  -- actual profile operators
  have hPHn (k : Fin 3) : ‖PH δr Ar p q k x‖ ≤ M :=
    (hEHc k _ hx).trans hHM
  have hPLn (i : Fin 3) : ‖PL δr Ar p q x i‖ ≤ M := by
    have heq := ActualHigherSCoefficientBounds.profileLow_eq_canonical
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hJac δr Ar p hδr hAr q hq x hx i
    exact (congrArg (fun A : Half →L[ℝ] Neg => ‖A‖) heq).le.trans ((hELc i _ hx).trans hEM)
  -- differentiated profile along X_i, by the chain rule
  have hDn (i j : Fin 3) :
      ‖fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i)‖ ≤ M := by
    have hEd : DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x) :=
      (Cm.germHigh j _ hx).differentiableAt (by simp)
    change ‖fderiv ℝ ((EH j) ∘ (Tq δr Ar p q)) x (referenceMetricGramFrame g L (q,x) i)‖ ≤ M
    exact (norm_fderiv_comp_apply_le (EH j) (Tq δr Ar p q) x
      (referenceMetricGramFrame g L (q,x) i) CH1 CT CX
      hEd hTd hCH10 hCT0' (hdEHc j _ hx) hT1 (hXn i)).trans hDM
  -- Lemma A for every exact Second row
  have hZ (i j : Fin 3) :
      ‖ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
        (PH δr Ar p q) (PL δr Ar p q x) x i j‖ ≤ 9*M^3*actualReferenceBeta g L q δr Ar p x :=
    norm_row_shape_le (JL : Half →L[ℝ] Neg)
      (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i))
      (referenceLowerHorizontalAngularL g L q x i)
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
      (PL δr Ar p q x i)
      (referenceHighHorizontalAngularL g L q x j)
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
      (PH δr Ar p q j x) (fun k => PH δr Ar p q k x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x j)
      (fun k => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j)
      M (actualReferenceBeta g L q δr Ar p x) hM hβ
      (hJN.trans hNM) (hDn i j) (hOlo i) (hBlN.trans hNM) (hPLn i) (hOhi j) (hBhN.trans hNM)
      (hPHn j) hPHn (hf i) (hf j) (fun k => hΓ i k j)
  -- Lemma B on the exact complete coefficient
  have hQ (i j : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M :=
    ((hQc q hq x hxK i j).1).trans hQM
  have hb (i : Fin 3) : |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M := by
    have h := hbc i (q,x) hqx
    rw [Real.norm_eq_abs] at h
    exact h.trans hbM
  have hfin := norm_zeroCoefficient_le (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
      (PH δr Ar p q) (PL δr Ar p q x) x)
    (fun j => PH δr Ar p q j x) (PL δr Ar p q x) Alo Ahi
    M (actualReferenceBeta g L q δr Ar p x) hM hβ hr0 hsmall
    (hJN.trans hNM) hQ hb hZ hPHn hPLn (fun i => (hAlN i).trans hNM) (fun j => (hAhN j).trans hNM)
  exact hfin

/-- Final actual producer: one retained radius/room/Jacobian guard from the existing
`exists_retained_common_formation_room` BEFORE `g2`, then for every admissible `g2`
one `K` before all profiles. Only the explicit `hL : 0 < L` is added. -/
theorem exists_retained_actual_zero_coefficient_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0)
    (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ, (∀ z ∈ commonRoom y0 ρ δ, Jac z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
        ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
        1 ≤ actualReferenceBeta g L q δr Ar p x →
        referenceRadius δr Ar p L x * (actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
        ‖CZ g2 δr Ar p q x‖ ≤ K * referenceRadius δr Ar p L x := by
  have hFull := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,Cm,hJac⟩
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_zero_coefficient_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac hL g2 hg2

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientBounds
