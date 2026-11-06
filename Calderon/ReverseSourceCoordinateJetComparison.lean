import Calderon.ActualCoordinateOrderedH8
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Set Filter
namespace OAI.AnisotropicCalderon.ReverseSourceCoordinateJetComparison
open PrincipalCommutator ReferenceDensityBounds CoordinateBootstrapJets ActualCoordinateOrderedH8

def sourceCanonicalCoordinatePartial (alpha : Fin 3 → Fin 11) (f : R3 → ℝ) : R3 → ℝ :=
  ((coordinateDerivative 0)^[(alpha 0).val])
    (((coordinateDerivative 1)^[(alpha 1).val])
      (((coordinateDerivative 2)^[(alpha 2).val]) f))

def sourceMultiIndexOrder (alpha : Fin 3 → Fin 11) : ℕ := ∑ k, (alpha k).val

def sourceCoordinateJetSum (f : R3 → ℝ) (x : R3) : ℝ :=
  ∑ alpha : Fin 3 → Fin 11,
    if sourceMultiIndexOrder alpha ≤ 10 then |sourceCanonicalCoordinatePartial alpha f x| else 0

lemma sourceCoordinateJetSum_nonneg (f : R3 → ℝ) (x : R3) :
    0 ≤ sourceCoordinateJetSum f x := by
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)

lemma norm_multilinear_le_coordinate_sum (n : ℕ) (T : R3 [×n]→L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ w : Fin n → Fin 3, ‖T (fun i => coordinateDirection (w i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have hv (i : Fin n) : (∑ k : Fin 3, (v i) k • coordinateDirection k) = v i := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
      using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (v i)
  have he : T v = ∑ w : Fin n → Fin 3,
      (∏ i : Fin n, (v i) (w i)) • T (fun i => coordinateDirection (w i)) := by
    calc T v = T (fun i => ∑ k : Fin 3, (v i) k • coordinateDirection k) := by simp only [hv]
      _ = ∑ w : Fin n → Fin 3, T (fun i => (v i) (w i) • coordinateDirection (w i)) :=
        T.toMultilinearMap.map_sum _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        exact T.toMultilinearMap.map_smul_univ _ _
  rw [he]
  calc ‖∑ w : Fin n → Fin 3,
        (∏ i : Fin n, (v i) (w i)) • T (fun i => coordinateDirection (w i))‖
      ≤ ∑ w : Fin n → Fin 3,
          ‖(∏ i : Fin n, (v i) (w i)) • T (fun i => coordinateDirection (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ w : Fin n → Fin 3,
        ‖T (fun i => coordinateDirection (w i))‖ * ∏ i : Fin n, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => PiLp.norm_apply_le (v i) (w i)))
        (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

lemma iteratedFDeriv_coordinate_eq_word (n : ℕ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (w : Fin n → Fin 3) (x : R3) :
    iteratedFDeriv ℝ n f x (fun i => coordinateDirection (w i)) =
      coordinateWordPartial (List.ofFn w) f x := by
  induction n generalizing x with
  | zero => simp [coordinateWordPartial]
  | succ n ih =>
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      hf.contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun y : R3 => iteratedFDeriv ℝ n f y
        (Fin.tail (fun i => coordinateDirection (w i)))) =
        coordinateWordPartial (List.ofFn (Fin.tail w)) f := by
      funext y
      exact ih (Fin.tail w) y
    rw [he, List.ofFn_succ]
    rfl

def sourceWordMultiIndex (w : List (Fin 3)) (hw : w.length ≤ 10) : Fin 3 → Fin 11 :=
  fun k => ⟨w.count k, by have hc : w.count k ≤ w.length := List.count_le_length; omega⟩

lemma sourceWordMultiIndex_order (w : List (Fin 3)) (hw : w.length ≤ 10) :
    sourceMultiIndexOrder (sourceWordMultiIndex w hw) = w.length :=
  coordinateWord_count_sum w

lemma coordinateWordPartial_eq_sourceCanonical (w : List (Fin 3)) (hw : w.length ≤ 10)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    coordinateWordPartial w f = sourceCanonicalCoordinatePartial (sourceWordMultiIndex w hw) f := by
  rw [coordinateWordPartial_eq_count_iterates w f hf]
  rfl

lemma abs_coordinateWordPartial_le_source_sum (w : List (Fin 3)) (hw : w.length ≤ 10)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    |coordinateWordPartial w f x| ≤ sourceCoordinateJetSum f x := by
  have ha : sourceMultiIndexOrder (sourceWordMultiIndex w hw) ≤ 10 := by
    rw [sourceWordMultiIndex_order]; exact hw
  have hs := Finset.single_le_sum
    (s := Finset.univ) (a := sourceWordMultiIndex w hw)
    (f := fun a : Fin 3 → Fin 11 =>
      if sourceMultiIndexOrder a ≤ 10 then |sourceCanonicalCoordinatePartial a f x| else 0)
    (fun a _ => by split_ifs <;> positivity) (Finset.mem_univ _)
  simpa only [ite_eq_left ha, sourceCoordinateJetSum,
    coordinateWordPartial_eq_sourceCanonical w hw f hf] using hs

theorem norm_iteratedFDeriv_le_sourceCoordinateJetSum (n : ℕ) (hn : n ≤ 10)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (3 : ℝ)^10 * sourceCoordinateJetSum f x := by
  have hS := sourceCoordinateJetSum_nonneg f x
  calc ‖iteratedFDeriv ℝ n f x‖
      ≤ ∑ w : Fin n → Fin 3, ‖iteratedFDeriv ℝ n f x
          (fun i => coordinateDirection (w i))‖ := norm_multilinear_le_coordinate_sum n _
    _ ≤ ∑ _w : Fin n → Fin 3, sourceCoordinateJetSum f x := by
      apply Finset.sum_le_sum
      intro w _
      rw [iteratedFDeriv_coordinate_eq_word n f hf w x, Real.norm_eq_abs]
      exact abs_coordinateWordPartial_le_source_sum (List.ofFn w) (by simpa using hn) f hf x
    _ = (3 : ℝ)^n * sourceCoordinateJetSum f x := by
      simp [Fintype.card_fin]
    _ ≤ (3 : ℝ)^10 * sourceCoordinateJetSum f x :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hS

theorem exists_sourceCoordinateJetComparison :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : R3 → ℝ), ContDiff ℝ ∞ f → ∀ x : R3,
      ∀ n : ℕ, n ≤ 10 → ‖iteratedFDeriv ℝ n f x‖ ≤ C * sourceCoordinateJetSum f x := by
  exact ⟨3^10, by norm_num, fun f hf x n hn =>
    norm_iteratedFDeriv_le_sourceCoordinateJetSum n hn f hf x⟩

lemma exists_global_smooth_germ_of_contDiffOn (U : Set R3) (hU : IsOpen U)
    (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U) :
    ∃ g : R3 → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨r/4, r/2, by positivity, by linarith⟩
  let g : R3 → ℝ := fun y => b y * f y
  have hbU : tsupport (b : R3 → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [b]; linarith)).trans hrU
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
    · have hn : y ∉ tsupport (b : R3 → ℝ) := fun h => hy (hbU h)
      have he : g =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with z hz
        simp only [g, hz, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨g, hg, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  simp only [g, hy, Pi.one_apply, one_mul]

lemma eventuallyEq_coordinateDerivative (k : Fin 3) {f g : R3 → ℝ} {x : R3}
    (h : f =ᶠ[𝓝 x] g) : coordinateDerivative k f =ᶠ[𝓝 x] coordinateDerivative k g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (coordinateDirection k)) hy

lemma eventuallyEq_coordinateDerivative_iterate (k : Fin 3) (n : ℕ)
    {f g : R3 → ℝ} {x : R3} (h : f =ᶠ[𝓝 x] g) :
    ((coordinateDerivative k)^[n]) f =ᶠ[𝓝 x] ((coordinateDerivative k)^[n]) g := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact eventuallyEq_coordinateDerivative k ih

lemma sourceCoordinateJetSum_eq_of_eventuallyEq {f g : R3 → ℝ} {x : R3}
    (h : f =ᶠ[𝓝 x] g) : sourceCoordinateJetSum f x = sourceCoordinateJetSum g x := by
  apply Finset.sum_congr rfl
  intro a _
  have ha := eventuallyEq_coordinateDerivative_iterate 0 (a 0).val
    (eventuallyEq_coordinateDerivative_iterate 1 (a 1).val
      (eventuallyEq_coordinateDerivative_iterate 2 (a 2).val h))
  change (if sourceMultiIndexOrder a ≤ 10 then |sourceCanonicalCoordinatePartial a f x| else 0) = _
  rw [show sourceCanonicalCoordinatePartial a f x = sourceCanonicalCoordinatePartial a g x from
    ha.eq_of_nhds]

theorem norm_iteratedFDeriv_le_sourceCoordinateJetSum_on (U : Set R3) (hU : IsOpen U)
    (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U)
    (n : ℕ) (hn : n ≤ 10) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (3 : ℝ)^10 * sourceCoordinateJetSum f x := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_germ_of_contDiffOn U hU f hf x hx
  have hD : iteratedFDeriv ℝ n g x = iteratedFDeriv ℝ n f x :=
    (he.iteratedFDeriv ℝ n).eq_of_nhds
  have hS := sourceCoordinateJetSum_eq_of_eventuallyEq he
  rw [← hD, ← hS]
  exact norm_iteratedFDeriv_le_sourceCoordinateJetSum n hn g hg x

theorem sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on (U : Set R3) (hU : IsOpen U)
    (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U) :
    (∑ n ∈ Finset.range 11, ‖iteratedFDeriv ℝ n f x‖) ≤
      (11 * (3 : ℝ)^10) * sourceCoordinateJetSum f x := by
  calc (∑ n ∈ Finset.range 11, ‖iteratedFDeriv ℝ n f x‖)
      ≤ ∑ _n ∈ Finset.range 11, (3 : ℝ)^10 * sourceCoordinateJetSum f x := by
        apply Finset.sum_le_sum
        intro n hn
        exact norm_iteratedFDeriv_le_sourceCoordinateJetSum_on U hU f hf x hx n
          (by have := Finset.mem_range.mp hn; omega)
    _ = _ := by simp; ring

/-- Definitionally the manuscript's literal scalar source-coordinate RHS. -/
theorem sourceCoordinateJetSum_eq_literal (f : R3 → ℝ) (x : R3) :
    sourceCoordinateJetSum f x =
      ∑ alpha : Fin 3 → Fin 11,
        if (∑ j : Fin 3, (alpha j).val) ≤ 10 then
          |(((coordinateDerivative 0)^[(alpha 0).val])
            (((coordinateDerivative 1)^[(alpha 1).val])
              (((coordinateDerivative 2)^[(alpha 2).val]) f))) x| else 0 := rfl

/-- Universal constant comes before the room, field, and point. -/
theorem exists_sourceCoordinateJetSumComparison_on :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set R3), IsOpen U →
      ∀ (f : R3 → ℝ), ContDiffOn ℝ ∞ f U → ∀ x ∈ U,
        (∑ n ∈ Finset.range 11, ‖iteratedFDeriv ℝ n f x‖) ≤
          C * sourceCoordinateJetSum f x := by
  exact ⟨11 * 3^10, by norm_num, fun U hU f hf x hx =>
    sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on U hU f hf x hx⟩

/-- The same pointwise room bound, summed over the same five fixed scalar fields. -/
theorem five_source_sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on
    (U : Set R3) (hU : IsOpen U) (F : Fin 5 → R3 → ℝ)
    (hF : ∀ k, ContDiffOn ℝ ∞ (F k) U) (x : R3) (hx : x ∈ U) :
    (∑ k : Fin 5, ∑ n ∈ Finset.range 11, ‖iteratedFDeriv ℝ n (F k) x‖) ≤
      (11 * (3 : ℝ)^10) * ∑ k : Fin 5, sourceCoordinateJetSum (F k) x := by
  calc (∑ k : Fin 5, ∑ n ∈ Finset.range 11, ‖iteratedFDeriv ℝ n (F k) x‖)
      ≤ ∑ k : Fin 5, (11 * (3 : ℝ)^10) * sourceCoordinateJetSum (F k) x := by
        exact Finset.sum_le_sum (fun k _ =>
          sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on U hU (F k) (hF k) x hx)
    _ = _ := by rw [Finset.mul_sum]

end OAI.AnisotropicCalderon.ReverseSourceCoordinateJetComparison

#print axioms OAI.AnisotropicCalderon.ReverseSourceCoordinateJetComparison.exists_sourceCoordinateJetComparison
#print axioms OAI.AnisotropicCalderon.ReverseSourceCoordinateJetComparison.exists_sourceCoordinateJetSumComparison_on
#print axioms OAI.AnisotropicCalderon.ReverseSourceCoordinateJetComparison.five_source_sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on

