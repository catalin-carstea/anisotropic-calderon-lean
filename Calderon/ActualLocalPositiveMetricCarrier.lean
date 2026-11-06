import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.NativeSourceChartPullbackSmoothness
import Calderon.NativeSourceChartPullbackPositivity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  NativeSourceChartCalculus

theorem exists_admissible_metric_eq_on_local_closed_ball
    (g : MatrixField) (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hg : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hPos : ∀ x ∈ U, (g x).PosDef) :
    ∃ a : ℝ, 0 < a ∧ a ≤ (1/4 : ℝ) ∧ closedBall (0 : R3) a ⊆ U ∧
      ∃ G : MatrixField, IsAdmissibleMetric G ∧ EqOn G g (closedBall (0 : R3) a) := by
  -- nested radii a < 2a < ε, with 2a ≤ 1/2 < 1
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨a, ha, haε, ha4⟩ : ∃ a : ℝ, 0 < a ∧ 2 * a < ε ∧ a ≤ (1/4 : ℝ) :=
    ⟨min (ε / 4) (1 / 4), lt_min (by linarith) (by norm_num),
      by have := min_le_left (ε / 4) (1 / 4); linarith, min_le_right _ _⟩
  have hBU : closedBall (0 : R3) (2 * a) ⊆ U :=
    (closedBall_subset_ball haε).trans hεU
  have haU : closedBall (0 : R3) a ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hBU
  -- smooth cutoff: one on closedBall 0 a, zero off ball 0 (2a)
  obtain ⟨φ, hφIn, hφOut⟩ : ∃ φ : ContDiffBump (0 : R3), φ.rIn = a ∧ φ.rOut = 2 * a :=
    ⟨⟨a, 2 * a, ha, by linarith⟩, rfl, rfl⟩
  have hφOne : ∀ y ∈ closedBall (0 : R3) a, φ y = 1 := by
    intro y hy
    apply φ.one_of_mem_closedBall
    rw [hφIn]
    exact hy
  have hφZero : ∀ y : R3, y ∉ closedBall (0 : R3) (2 * a) → φ y = 0 := by
    intro y hy
    apply φ.zero_of_le_dist
    rw [hφOut]
    rw [mem_closedBall, not_le] at hy
    exact hy.le
  -- the blended matrix field
  obtain ⟨G, hGdef⟩ : ∃ G : MatrixField,
      ∀ x, G x = φ x • g x + (1 - φ x) • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    ⟨fun x => φ x • g x + (1 - φ x) • (1 : Matrix (Fin 3) (Fin 3) ℝ), fun x => rfl⟩
  have hGij : ∀ i j : Fin 3, (fun x => G x i j) =
      fun x => φ x * g x i j + (1 - φ x) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    funext x
    rw [hGdef x]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hProd : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => φ x * g x i j) := by
    intro i j
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (φ.contDiff (n := ⊤)).contDiffAt.mul ((hg i j).contDiffAt (hU.mem_nhds hx))
    · have hFar : x ∈ (closedBall (0 : R3) (2 * a))ᶜ := fun hxB => hx (hBU hxB)
      have hZero : (fun y => φ y * g y i j) =ᶠ[𝓝 x] (fun _ : R3 => (0 : ℝ)) := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hFar] with y hy
        simp only [hφZero y hy, zero_mul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : ℝ)) x).congr_of_eventuallyEq
        hZero
  have hGsmooth : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => G x i j) := by
    intro i j
    rw [hGij i j]
    exact (hProd i j).add ((contDiff_const.sub (φ.contDiff (n := ⊤))).mul contDiff_const)
  have hGpos : ∀ x, (G x).PosDef := by
    intro x
    rw [hGdef x]
    by_cases hφx : φ x = 0
    · rw [hφx, zero_smul, sub_zero, one_smul, zero_add]
      exact Matrix.PosDef.one
    · have hxU : x ∈ U := by
        by_contra hxU
        exact hφx (hφZero x (fun hxB => hxU (hBU hxB)))
      have hφpos : 0 < φ x := lt_of_le_of_ne (φ.nonneg' x) (Ne.symm hφx)
      have hφle : 0 ≤ 1 - φ x := sub_nonneg.mpr φ.le_one
      exact ((hPos x hxU).smul hφpos).add_posSemidef
        ((Matrix.PosSemidef.one (n := Fin 3) (R := ℝ)).smul hφle)
  refine ⟨a, ha, ha4, haU, G,
    { smooth := hGsmooth
      posDef := hGpos
      euclidean_exterior := ?_ }, ?_⟩
  · -- for ‖x‖ ≥ 1 the cutoff vanishes, so G x = 1
    intro x hx
    have hx1 : (1 : ℝ) ≤ ‖x‖ := by
      first
      | exact hx
      | exact le_of_lt hx
      | simpa [mem_ball, dist_zero_right, not_lt] using hx
      | simpa using hx
    have hφx : φ x = 0 := hφZero x (fun hxB => by
      rw [mem_closedBall, dist_zero_right] at hxB
      linarith)
    rw [hGdef x, hφx, zero_smul, sub_zero, one_smul, zero_add]
  · intro x hx
    rw [hGdef x, hφOne x hx, one_smul, sub_self, zero_smul, add_zero]

theorem exists_admissible_harmonic_coordinate_carrier_near_origin
    (g : MatrixField) (hg : IsAdmissibleMetric g) (Xi : R3 → R3)
    (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hXi : ContDiffOn ℝ ∞ Xi U)
    (hInjective : ∀ x ∈ U, Function.Injective (fderiv ℝ Xi x))
    (hNormalized : pullbackMetric g Xi 0 = 1)
    (hHarmonic : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g Xi) (fun z => z i)) x = 0) :
    ∃ a : ℝ, 0 < a ∧ a ≤ (1/4 : ℝ) ∧ closedBall (0 : R3) a ⊆ U ∧
      ∃ G : MatrixField, IsAdmissibleMetric G ∧
        EqOn G (pullbackMetric g Xi) (closedBall (0 : R3) a) ∧ G 0 = 1 ∧
        ∀ i : Fin 3, ∀ x ∈ ball (0 : R3) a,
          coordinateFluxDivergence (metricDivergenceFlux G (fun z => z i)) x = 0 := by
  have hSmooth : ContDiffOn ℝ ∞ (pullbackMetric g Xi) U :=
    contDiffOn_native_source_chart_pullbackMetric g hg Xi U hU hXi
  have hEntries : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (fun x => pullbackMetric g Xi x i j) U := by
    intro i j
    first
    | exact contDiffOn_pi.mp (contDiffOn_pi.mp hSmooth i) j
    | exact (LinearMap.toContinuousLinearMap
        (Matrix.entryLinearMap ℝ ℝ i j : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℝ)).contDiff.comp_contDiffOn
          hSmooth
    | exact (contDiff_apply_apply i j).comp_contDiffOn hSmooth
    | exact ((ContinuousLinearMap.proj (R := ℝ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) i)).contDiff.comp_contDiffOn
          hSmooth
  have hPos : ∀ x ∈ U, (pullbackMetric g Xi x).PosDef := fun x hx =>
    pullbackMetric_posDef_of_injective_fderiv g hg Xi x (hInjective x hx)
  obtain ⟨a, ha, ha4, haU, G, hG, hGeq⟩ :=
    exists_admissible_metric_eq_on_local_closed_ball (pullbackMetric g Xi) U hU h0 hEntries hPos
  refine ⟨a, ha, ha4, haU, G, hG, hGeq, ?_, ?_⟩
  · exact (hGeq (mem_closedBall_self ha.le)).trans hNormalized
  · intro i x hx
    have hMetric : G =ᶠ[𝓝 x] pullbackMetric g Xi := by
      filter_upwards [isOpen_ball.mem_nhds hx] with z hz
      exact hGeq (ball_subset_closedBall hz)
    rw [coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      G (pullbackMetric g Xi) (fun z => z i) x hMetric]
    exact hHarmonic i x (haU (ball_subset_closedBall hx))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
