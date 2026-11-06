import Calderon.RadiusTwoEuclideanCollar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! EXPANSION.json precedes compact-band barrier selection, AE order upgrade, and boundary squeeze. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

lemma exists_radialBarrier_bound_on_compact_innerBand
    (U : R3 → ℝ) (a0 a b : ℝ) (h0a : a0 < a) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hU : ContinuousOn U (radiusTwoCollarOpens a0 : Set R3)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : R3, a ≤ ‖x‖ → ‖x‖ ≤ b → |U x| ≤ M*(4-‖x‖^2) := by
  let K : Set R3 := {x : R3 | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : R3) b).of_isClosed_subset hKclosed
    (fun x hx => mem_closedBall_zero_iff.mpr hx.2)
  have hKsub : K ⊆ (radiusTwoCollarOpens a0 : Set R3) := fun x hx =>
    ⟨h0a.trans_le hx.1,hx.2.trans_lt hb2⟩
  obtain ⟨C,hC⟩ := hK.bddAbove_image (hU.abs.mono hKsub)
  have hD : 0 < 4-b^2 := by
    have hSq := (sq_lt_sq₀ hb0 (by norm_num : (0 : ℝ) ≤ 2)).mpr hb2
    norm_num at hSq
    linarith
  let M : ℝ := max 0 C / (4-b^2)
  have hM : 0 ≤ M := div_nonneg (le_max_left 0 C) hD.le
  have hMD : M*(4-b^2) = max 0 C := div_mul_cancel₀ _ hD.ne'
  refine ⟨M,hM,?_⟩
  intro x hax hxb
  have hSq : ‖x‖^2 ≤ b^2 := (sq_le_sq₀ (norm_nonneg x) hb0).mpr hxb
  calc
    |U x| ≤ C := hC ⟨x,⟨hax,hxb⟩,rfl⟩
    _ ≤ max 0 C := le_max_right 0 C
    _ = M*(4-b^2) := hMD.symm
    _ ≤ M*(4-‖x‖^2) := mul_le_mul_of_nonneg_left (sub_le_sub_left hSq 4) hM

lemma leOn_open_of_ae_le_of_continuousOn (V : Opens R3) (f g : R3 → ℝ)
    (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (hfg : ∀ᵐ x ∂(volume : Measure R3).restrict V, f x ≤ g x) :
    ∀ x ∈ V, f x ≤ g x := by
  have hEq : (fun x : R3 => max (f x) (g x)) =ᵐ[((volume : Measure R3).restrict V)] g := by
    filter_upwards [hfg] with x hx
    exact max_eq_right hx
  have hMax : ContinuousOn (fun x : R3 => max (f x) (g x)) V := by
    change ContinuousOn (fun x : R3 => f x ⊔ g x) V
    exact hf.sup hg
  have hPoint := Measure.eqOn_open_of_ae_eq hEq V.isOpen hMax hg
  intro x hx
  exact (max_eq_right_iff.mp (hPoint hx))

lemma continuousAt_zeroExtension_of_radialBarrier
    (U : R3 → ℝ) (a M : ℝ) (ha2 : a < 2) (hM : 0 ≤ M)
    (hBound : ∀ x ∈ radiusTwoCollarOpens a, |U x| ≤ M*(4-‖x‖^2))
    (y : R3) (hy : ‖y‖ = 2) :
    ContinuousAt (fun x : R3 => if ‖x‖ < 2 then U x else 0) y := by
  let F : R3 → ℝ := fun x => if ‖x‖ < 2 then U x else 0
  have hNear : ∀ᶠ x in 𝓝 y, a < ‖x‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds (by
      change a < ‖y‖
      rw [hy]
      exact ha2)
  have hDom : ∀ᶠ x in 𝓝 y, |F x| ≤ M*|4-‖x‖^2| := by
    filter_upwards [hNear] with x hx
    by_cases hIn : ‖x‖ < 2
    · have hSq := (sq_le_sq₀ (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 2)).mpr hIn.le
      have hNonneg : 0 ≤ 4-‖x‖^2 := by norm_num at hSq; linarith
      simpa only [F,if_pos hIn,abs_of_nonneg hNonneg] using hBound x ⟨hx,hIn⟩
    · simp only [F,if_neg hIn,abs_zero]
      exact mul_nonneg hM (abs_nonneg _)
  have hCont : Continuous (fun x : R3 => M*|4-‖x‖^2|) :=
    continuous_const.mul ((continuous_const.sub (continuous_norm.pow 2)).abs)
  have hRhs : Tendsto (fun x : R3 => M*|4-‖x‖^2|) (𝓝 y) (𝓝 0) := by
    have hT : Tendsto (fun x : R3 => M*|4-‖x‖^2|) (𝓝 y) (𝓝 (M*|4-‖y‖^2|)) :=
      hCont.continuousAt
    have hEval : M*|4-‖y‖^2| = 0 := by
      rw [hy]
      norm_num
    rw [hEval] at hT
    exact hT
  have hAbs : Tendsto (fun x : R3 => |F x|) (𝓝 y) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun x => abs_nonneg (F x))) hDom hRhs
  have hF : Tendsto F (𝓝 y) (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).mpr hAbs
  have hFy : F y = 0 := by simp only [F,hy,lt_self_iff_false,if_false]
  change Tendsto F (𝓝 y) (𝓝 (F y))
  rw [hFy]
  exact hF

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_radialBarrier_bound_on_compact_innerBand
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.leOn_open_of_ae_le_of_continuousOn
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuousAt_zeroExtension_of_radialBarrier
