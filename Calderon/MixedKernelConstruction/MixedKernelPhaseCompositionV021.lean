import Calderon.MixedKernelConstruction.C3PartialJets
import Calderon.ActualRadiusTwoGreenL2Coefficient
import Calderon.CollaboratorUCPIdentityOct17
import Calderon.MixedKernelConstruction.MixedKernelConstructionSupportV015
import Calderon.StrictWeightNativeProductHessian
import Calderon.StrictWeightPrescribedMetricJets
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Dual.Lemmas
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry

theorem v021_original_kernel_joint_regular : OriginalKernelJointRegularityGoal :=
  v015_original_kernel_joint_regular
theorem v021_normal_packet_cover_exists : NativeNormalPacketCoverGoal :=
  v015_normal_packet_cover_exists
theorem v021_initial_cross_product : InitialCrossProductGoal := v015_initial_cross_product

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-!
## C4 strict phase composition (S1–S6)

The strict-phase chain rule, the compact margin, the zero-level identity and
level-interval monotonicity. Nothing here is an endpoint premise.
-/
section C4StrictPhaseComposition
open MetricVolume
open scoped ContDiff

/-- S1: Christoffel chain rule for `psi = theta - kappa theta^2`. -/
theorem christoffelHess_strictPhase (G A : Fin 3 → Fin 3 → R3 → ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (x : R3) (i j : Fin 3) :
    StrictWeightCarleman.christoffelHess G A (fun y => θ y - κ * θ y ^ 2) x i j =
      (1 - 2 * κ * θ x) * StrictWeightCarleman.christoffelHess G A θ x i j -
        2 * κ * OAI.AnisotropicCalderon.pd i θ x * OAI.AnisotropicCalderon.pd j θ x := by
  simp only [StrictWeightCarleman.christoffelHess, CutoffCommutator.pd_pd_strictPhase hθ κ,
    CutoffCommutator.pd_strictPhase hθ κ]
  have hsum : ∀ C : Fin 3 → ℝ, ∑ k, C k * ((1 - 2 * κ * θ x) * pd k θ x) =
      (1 - 2 * κ * θ x) * ∑ k, C k * pd k θ x := by
    intro C
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  ring

/-- S2: the SAME native metric Hessian obeys the strict-phase chain rule. -/
theorem metricHessianMatrix_strictPhase (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun y => g y i j)) (hp : ∀ y, (g y).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (x : R3) (i j : Fin 3) :
    metricHessianMatrix g (fun y => θ y - κ * θ y ^ 2) x i j =
      (1 - 2 * κ * θ x) * metricHessianMatrix g θ x i j -
        2 * κ * OAI.AnisotropicCalderon.pd i θ x * OAI.AnisotropicCalderon.pd j θ x := by
  have hψ : ContDiff ℝ ∞ (fun y => θ y - κ * θ y ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  rw [metricHessianMatrix_eq_christoffelHess g hs hp hψ,
    metricHessianMatrix_eq_christoffelHess g hs hp hθ]
  exact christoffelHess_strictPhase _ _ hθ κ x i j

/-- S3: at the zero level the gradient is unchanged. -/
theorem pd_strictPhase_of_zero {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) {x : R3}
    (h0 : θ x = 0) (i : Fin 3) :
    OAI.AnisotropicCalderon.pd i (fun y => θ y - κ * θ y ^ 2) x =
      OAI.AnisotropicCalderon.pd i θ x := by
  rw [CutoffCommutator.pd_strictPhase hθ κ i x, h0]
  ring

/-- S3: at the zero level the SAME metric Hessian loses only `2 kappa dθ ⊗ dθ`. -/
theorem metricHessianMatrix_strictPhase_of_zero (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun y => g y i j)) (hp : ∀ y, (g y).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) {x : R3} (h0 : θ x = 0) (i j : Fin 3) :
    metricHessianMatrix g (fun y => θ y - κ * θ y ^ 2) x i j =
      metricHessianMatrix g θ x i j -
        2 * κ * OAI.AnisotropicCalderon.pd i θ x * OAI.AnisotropicCalderon.pd j θ x := by
  rw [metricHessianMatrix_strictPhase g hs hp hθ κ x i j, h0]
  ring

/-- Quadratic form of a coordinate matrix. -/
def coordQuad (H : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, H i j * v i * v j

/-- S3: on directions `e, v` with `ℓ v = 0`, the strictness expression of `psi` at the
zero level equals that of `theta` minus `2 kappa (ℓ e)^2`. -/
theorem strictness_strictPhase_of_zero (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun y => g y i j)) (hp : ∀ y, (g y).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) {x : R3} (h0 : θ x = 0)
    (e v : Fin 3 → ℝ) (hv : ∑ i, OAI.AnisotropicCalderon.pd i θ x * v i = 0) :
    coordQuad (metricHessianMatrix g (fun y => θ y - κ * θ y ^ 2) x) e +
        coordQuad (metricHessianMatrix g (fun y => θ y - κ * θ y ^ 2) x) v =
      coordQuad (metricHessianMatrix g θ x) e + coordQuad (metricHessianMatrix g θ x) v -
        2 * κ * (∑ i, OAI.AnisotropicCalderon.pd i θ x * e i) ^ 2 := by
  have hrank : ∀ w : Fin 3 → ℝ,
      coordQuad (metricHessianMatrix g (fun y => θ y - κ * θ y ^ 2) x) w =
        coordQuad (metricHessianMatrix g θ x) w -
          2 * κ * (∑ i, OAI.AnisotropicCalderon.pd i θ x * w i) ^ 2 := by
    intro w
    simp only [coordQuad, metricHessianMatrix_strictPhase_of_zero g hs hp hθ κ h0,
      Fin.sum_univ_three]
    ring
  rw [hrank e, hrank v, hv]
  ring


/-- S4: positive margin of a positive continuous function on a compact set
(empty set handled explicitly with margin `1`). -/
theorem exists_pos_margin_of_isCompact {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) {F : E → ℝ} (hF : ContinuousOn F K) (hpos : ∀ v ∈ K, 0 < F v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ F v := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, by simp [hE]⟩
  · obtain ⟨v0, hv0, hmin⟩ := hK.exists_isMinOn hne hF
    exact ⟨F v0, hpos v0 hv0, fun v hv => hmin hv⟩



/-- S5: elementary common-kappa loss budget (scalar). -/
theorem exists_common_kappa_margin {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (d1 d2 : ℝ) : ∃ κ : ℝ, 0 < κ ∧
      2 * κ * d1 ^ 2 ≤ c1 / 2 ∧ 2 * κ * d2 ^ 2 ≤ c2 / 2 := by
  have hden1 : 0 < 4 * (1 + d1 ^ 2) := by positivity
  have hden2 : 0 < 4 * (1 + d2 ^ 2) := by positivity
  let κ : ℝ := min (c1 / (4 * (1 + d1 ^ 2))) (c2 / (4 * (1 + d2 ^ 2)))
  have hk : 0 < κ := lt_min (div_pos hc1 hden1) (div_pos hc2 hden2)
  have hb1 : κ * (4 * (1 + d1 ^ 2)) ≤ c1 :=
    (le_div_iff₀ hden1).mp (min_le_left _ _)
  have hb2 : κ * (4 * (1 + d2 ^ 2)) ≤ c2 :=
    (le_div_iff₀ hden2).mp (min_le_right _ _)
  refine ⟨κ, hk, ?_, ?_⟩
  · calc 2 * κ * d1 ^ 2 ≤ 2 * κ * (1 + d1 ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = κ * (4 * (1 + d1 ^ 2)) / 2 := by ring
      _ ≤ c1 / 2 := by linarith
  · calc 2 * κ * d2 ^ 2 ≤ 2 * κ * (1 + d2 ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = κ * (4 * (1 + d2 ^ 2)) / 2 := by ring
      _ ≤ c2 / 2 := by linarith

/-- S4+S5: ONE positive kappa giving both compact strictness margins `≥ c_i/2`. -/
theorem exists_common_kappa_compact_margins {E : Type*} [TopologicalSpace E]
    {K1 K2 : Set E} (hK1 : IsCompact K1) (hK2 : IsCompact K2) {F1 F2 : E → ℝ}
    (hF1 : ContinuousOn F1 K1) (hF2 : ContinuousOn F2 K2)
    (hp1 : ∀ v ∈ K1, 0 < F1 v) (hp2 : ∀ v ∈ K2, 0 < F2 v) (d1 d2 : ℝ) :
    ∃ c1 c2 κ : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < κ ∧
      (∀ v ∈ K1, c1 / 2 ≤ F1 v - 2 * κ * d1 ^ 2) ∧
      (∀ v ∈ K2, c2 / 2 ≤ F2 v - 2 * κ * d2 ^ 2) := by
  obtain ⟨c1, hc1, hm1⟩ := exists_pos_margin_of_isCompact hK1 hF1 hp1
  obtain ⟨c2, hc2, hm2⟩ := exists_pos_margin_of_isCompact hK2 hF2 hp2
  obtain ⟨κ, hk, h1, h2⟩ := exists_common_kappa_margin hc1 hc2 d1 d2
  refine ⟨c1, c2, κ, hc1, hc2, hk, fun v hv => ?_, fun v hv => ?_⟩
  · linarith [hm1 v hv]
  · linarith [hm2 v hv]

/-- S6: the source profile `t ↦ t - kappa t^2` is strictly increasing on the level
interval `|t| ≤ 1/(4 kappa)`. -/
theorem strictPhaseProfile_strictMonoOn {κ : ℝ} (hκ : 0 < κ) :
    StrictMonoOn (fun t : ℝ => t - κ * t ^ 2) (Set.Icc (-(1 / (4 * κ))) (1 / (4 * κ))) := by
  intro s hs t ht hst
  have hb : κ * (1 / (4 * κ)) = 1 / 4 := by field_simp
  have hs1 : κ * s ≤ 1 / 4 := hb ▸ mul_le_mul_of_nonneg_left hs.2 hκ.le
  have ht1 : κ * t ≤ 1 / 4 := hb ▸ mul_le_mul_of_nonneg_left ht.2 hκ.le
  have hfac : (t - κ * t ^ 2) - (s - κ * s ^ 2) = (t - s) * (1 - κ * s - κ * t) := by ring
  have hpos : 0 < (t - s) * (1 - κ * s - κ * t) :=
    mul_pos (sub_pos.mpr hst) (by linarith)
  show s - κ * s ^ 2 < t - κ * t ^ 2
  linarith


end C4StrictPhaseComposition

/-!
## C1: conformal Mgrad cancellation
Literal divergence coefficient `h * g⁻¹` versus the metric inverse `g⁻¹`. Every
derivative of `h` is kept until the exact characteristic cancellation.
-/
section C4ConformalMgrad
open scoped InnerProductSpace ContDiff Topology
open MetricOperator ConnectionError

/-- C1a: exact product rule for the native `Mgrad` under `a ↦ h a`, `X ↦ h X`. -/
theorem Mgrad_conformal (a : Fin 3 → Fin 3 → R3 → ℝ) (X : Fin 3 → R3 → ℝ) (h : R3 → ℝ)
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hX : ∀ j, ContDiff ℝ ∞ (X j))
    (hh : ContDiff ℝ ∞ h) (x : R3) (ξ : Fin 3 → ℝ) :
    OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * a i k y) (fun j y => h y * X j y) x ξ =
      h x ^ 2 * OAI.AnisotropicCalderon.Mgrad a X x ξ +
      4 * h x * (∑ i, ∑ l, a i l x * ξ l * OAI.AnisotropicCalderon.pd i h x) *
        (∑ j, X j x * ξ j) -
      2 * h x * (∑ j, X j x * OAI.AnisotropicCalderon.pd j h x) *
        OAI.AnisotropicCalderon.quad a x ξ := by
  have h1 : ∀ i j, OAI.AnisotropicCalderon.pd i (fun y => h y * X j y) x =
      OAI.AnisotropicCalderon.pd i h x * X j x +
        h x * OAI.AnisotropicCalderon.pd i (X j) x :=
    fun i j => OAI.AnisotropicCalderon.pd_mul hh (hX j) x
  have h2 : ∀ j i k, OAI.AnisotropicCalderon.pd j (fun y => h y * a i k y) x =
      OAI.AnisotropicCalderon.pd j h x * a i k x +
        h x * OAI.AnisotropicCalderon.pd j (a i k) x :=
    fun j i k => OAI.AnisotropicCalderon.pd_mul hh (ha i k) x
  simp only [OAI.AnisotropicCalderon.Mgrad, OAI.AnisotropicCalderon.quad, h1, h2,
    Fin.sum_univ_three]
  ring

/-- C1b: the native quadratic form scales by `h`. -/
theorem quad_conformal (a : Fin 3 → Fin 3 → R3 → ℝ) (h : R3 → ℝ) (x : R3) (ξ : Fin 3 → ℝ) :
    OAI.AnisotropicCalderon.quad (fun i k y => h y * a i k y) x ξ =
      h x * OAI.AnisotropicCalderon.quad a x ξ := by
  simp only [OAI.AnisotropicCalderon.quad, Fin.sum_univ_three]
  ring

/-- C1b: the native normalized-gradient field scales by `h`. -/
theorem bv_conformal (a : Fin 3 → Fin 3 → R3 → ℝ) (h f : R3 → ℝ) :
    OAI.AnisotropicCalderon.bv (fun i k y => h y * a i k y) f =
      fun j y => h y * OAI.AnisotropicCalderon.bv a f j y := by
  funext j y
  simp only [OAI.AnisotropicCalderon.bv, Fin.sum_univ_three]
  ring

/-- C1b: the native `Nf` scales by `h`. -/
theorem Nf_conformal (a : Fin 3 → Fin 3 → R3 → ℝ) (h f : R3 → ℝ) (x : R3) :
    OAI.AnisotropicCalderon.Nf (fun i k y => h y * a i k y) f x =
      h x * OAI.AnisotropicCalderon.Nf a f x := by
  simp only [OAI.AnisotropicCalderon.Nf, OAI.AnisotropicCalderon.bv, Fin.sum_univ_three]
  ring

/-- C1c: on the characteristic constraints the `dh` corrections cancel in the SUM. -/
theorem Mgrad_conformal_characteristic_sum (a : Fin 3 → Fin 3 → R3 → ℝ)
    (X : Fin 3 → R3 → ℝ) (h : R3 → ℝ)
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hX : ∀ j, ContDiff ℝ ∞ (X j))
    (hh : ContDiff ℝ ∞ h) (x : R3) (p ξ : Fin 3 → ℝ)
    (hsym : ∀ i l, a i l x = a l i x) (hXp : ∀ j, X j x = ∑ k, a j k x * p k)
    (hB : ∑ j, X j x * ξ j = 0)
    (hq : OAI.AnisotropicCalderon.quad a x ξ = OAI.AnisotropicCalderon.quad a x p) :
    OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * a i k y) (fun j y => h y * X j y) x p +
        OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * a i k y)
          (fun j y => h y * X j y) x ξ =
      h x ^ 2 * (OAI.AnisotropicCalderon.Mgrad a X x p +
        OAI.AnisotropicCalderon.Mgrad a X x ξ) := by
  have hS : (∑ i, ∑ l, a i l x * p l * OAI.AnisotropicCalderon.pd i h x) =
      ∑ j, X j x * OAI.AnisotropicCalderon.pd j h x := by
    simp only [hXp, Fin.sum_univ_three]
    rw [hsym 1 0, hsym 2 0, hsym 2 1]
    ring
  have hBp : (∑ j, X j x * p j) = OAI.AnisotropicCalderon.quad a x p := by
    simp only [hXp, OAI.AnisotropicCalderon.quad, Fin.sum_univ_three]
    ring
  rw [Mgrad_conformal a X h ha hX hh x p, Mgrad_conformal a X h ha hX hh x ξ, hS, hBp, hB, hq]
  ring

/-- C1d: metric-unit Hessian strictness gives raw strictness for the LITERAL
conformal coefficient `h * g⁻¹` with its own field `bv (h g⁻¹) f`, for any smooth
positive density `h`. Uses the native `strict_weight_inverseMetric_of_unitHessian`. -/
theorem strict_weight_conformal_inverseMetric_of_unitHessian
    (g : MatrixField) (h f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : R3)
    (hginv : ∀ i k, ContDiff ℝ ∞ (fun y => (g y)⁻¹ i k))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (hgrad : OAI.AnisotropicCalderon.grad f x ≠ 0) (hhx : 0 < h x)
    (hunit :
      let b : R3 := matrixOperatorMap ((g x)⁻¹)
        (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad f x))
      let e : R3 := (Real.sqrt ⟪metricOperatorField g x b, b⟫_ℝ)⁻¹ • b
      ∀ v : R3, ⟪metricOperatorField g x v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g x v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian f
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y) x e e +
          RadiusProfile.coordinateHessian f
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y) x v v) :
    ∀ ξ : Fin 3 → ℝ,
      (∑ j : Fin 3, OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k) f j x * ξ j)
          = 0 →
      OAI.AnisotropicCalderon.quad (fun i k y => h y * (g y)⁻¹ i k) x ξ =
        OAI.AnisotropicCalderon.Nf (fun i k y => h y * (g y)⁻¹ i k) f x →
      0 < OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * (g y)⁻¹ i k)
          (OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k) f) x
            (OAI.AnisotropicCalderon.grad f x) +
        OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * (g y)⁻¹ i k)
          (OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k) f) x ξ := by
  intro ξ hB hq
  have hbvC : ∀ j, ContDiff ℝ ∞
      (OAI.AnisotropicCalderon.bv (fun i k y => (g y)⁻¹ i k) f j) := by
    intro j
    unfold OAI.AnisotropicCalderon.bv
    exact ContDiff.sum fun k _ =>
      (hginv j k).mul (OAI.AnisotropicCalderon.contDiff_pd_apply hf)
  have hBe : (∑ j : Fin 3,
      OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k) f j x * ξ j) =
      h x * ∑ j : Fin 3, OAI.AnisotropicCalderon.bv (fun i k y => (g y)⁻¹ i k) f j x * ξ j := by
    simp only [OAI.AnisotropicCalderon.bv, Fin.sum_univ_three]
    ring
  have hB0 : (∑ j : Fin 3,
      OAI.AnisotropicCalderon.bv (fun i k y => (g y)⁻¹ i k) f j x * ξ j) = 0 := by
    rw [hBe] at hB
    exact (mul_eq_zero.mp hB).resolve_left hhx.ne'
  have hq0 : OAI.AnisotropicCalderon.quad (fun i k y => (g y)⁻¹ i k) x ξ =
      OAI.AnisotropicCalderon.Nf (fun i k y => (g y)⁻¹ i k) f x := by
    rw [quad_conformal (fun i k y => (g y)⁻¹ i k) h x ξ,
      Nf_conformal (fun i k y => (g y)⁻¹ i k) h f x] at hq
    exact mul_left_cancel₀ hhx.ne' hq
  have hraw := OAI.AnisotropicCalderon.strict_weight_inverseMetric_of_unitHessian
    g f hf x hg hp hs hgrad hunit ξ hB0 hq0
  have hNQ : OAI.AnisotropicCalderon.Nf (fun i k y => (g y)⁻¹ i k) f x =
      OAI.AnisotropicCalderon.quad (fun i k y => (g y)⁻¹ i k) x
        (OAI.AnisotropicCalderon.grad f x) := by
    simp only [OAI.AnisotropicCalderon.Nf, OAI.AnisotropicCalderon.bv,
      OAI.AnisotropicCalderon.grad, OAI.AnisotropicCalderon.quad, Fin.sum_univ_three]
    ring
  have hsym : ∀ i l, (g x)⁻¹ i l = (g x)⁻¹ l i := by
    intro i l
    simpa only [star_trivial] using hp.inv.isHermitian.apply l i
  have hc := Mgrad_conformal_characteristic_sum (fun i k y => (g y)⁻¹ i k)
    (OAI.AnisotropicCalderon.bv (fun i k y => (g y)⁻¹ i k) f) h hginv hbvC hh x
    (OAI.AnisotropicCalderon.grad f x) ξ hsym (fun j => rfl) hB0 (hq0.trans hNQ)
  refine lt_of_lt_of_eq (mul_pos (pow_pos hhx 2) hraw) ?_
  rw [bv_conformal (fun i k y => (g y)⁻¹ i k) h f]
  exact hc.symm

end C4ConformalMgrad
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
