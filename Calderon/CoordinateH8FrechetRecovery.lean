import Calderon.CoordinateBootstrapJets
import Calderon.ActualSourceSpatialMetricJetRecovery
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth ReferenceWeightedApproximation CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra

/-- The actual coordinate derivative is evaluation of the actual Frechet derivative
on the unit coordinate vector. -/
theorem coordH8Frechet_coordinateDerivative_eq (k : Fin 3) (f : R3 → ℝ) :
    coordinateDerivative k f = fun y => fderiv ℝ f y (ReferenceDensityBounds.coordinateDirection k) := by
  first
    | rfl
    | (funext y; rfl)
    | (funext y; simp [coordinateDerivative, directionalFDeriv])

theorem coordH8Frechet_contDiff_coordinateDerivative (k : Fin 3) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateDerivative k f) := by
  rw [coordH8Frechet_coordinateDerivative_eq]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- One coordinate derivative raises the Frechet jet order by one, with constant one. -/
theorem coordH8Frechet_norm_iteratedFDeriv_coordinateDerivative_le (k : Fin 3)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : R3) :
    ‖iteratedFDeriv ℝ n (coordinateDerivative k f) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hv : ‖ReferenceDensityBounds.coordinateDirection k‖ = 1 := by
    first
      | simp [ReferenceDensityBounds.coordinateDirection]
      | (unfold ReferenceDensityBounds.coordinateDirection; simp)
  have hnorm : ‖ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
    calc ‖ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k) z‖
        = ‖z (ReferenceDensityBounds.coordinateDirection k)‖ := rfl
      _ ≤ ‖z‖ * ‖ReferenceDensityBounds.coordinateDirection k‖ := z.le_opNorm _
      _ = 1 * ‖z‖ := by rw [hv, mul_one, one_mul]
  have hcomp : coordinateDerivative k f =
      (ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k)) ∘ fderiv ℝ f := by
    first
      | rfl
      | (funext y; rfl)
      | (rw [coordH8Frechet_coordinateDerivative_eq]; funext y; simp)
  rw [hcomp]
  calc ‖iteratedFDeriv ℝ n
        ((ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k)) ∘ fderiv ℝ f) x‖
      ≤ ‖ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k)‖ *
          ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
        (ContinuousLinearMap.apply ℝ ℝ (ReferenceDensityBounds.coordinateDirection k)).norm_iteratedFDeriv_comp_left
          hDf.contDiffAt (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
        first
          | rw [one_mul, norm_iteratedFDeriv_fderiv]
          | (rw [one_mul]; exact norm_iteratedFDeriv_fderiv)
          | simp [norm_iteratedFDeriv_fderiv]

/-- Iterated coordinate derivatives: smoothness and the order-shift contraction. -/
theorem coordH8Frechet_iterate (k : Fin 3) (j : ℕ) :
    ∀ f : R3 → ℝ, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ ((coordinateDerivative k)^[j] f) ∧
      ∀ (n : ℕ) (x : R3), ‖iteratedFDeriv ℝ n ((coordinateDerivative k)^[j] f) x‖ ≤
        ‖iteratedFDeriv ℝ (n + j) f x‖ := by
  induction j with
  | zero =>
    intro f hf
    refine ⟨?_, fun n x => ?_⟩
    · first | exact hf | simpa using hf
    · first | exact le_refl _ | simp
  | succ j ih =>
    intro f hf
    obtain ⟨hg, hbound⟩ := ih f hf
    have heq : (coordinateDerivative k)^[j + 1] f =
        coordinateDerivative k ((coordinateDerivative k)^[j] f) :=
      Function.iterate_succ_apply' _ _ _
    rw [heq]
    refine ⟨coordH8Frechet_contDiff_coordinateDerivative k _ hg, fun n x => ?_⟩
    calc ‖iteratedFDeriv ℝ n (coordinateDerivative k ((coordinateDerivative k)^[j] f)) x‖
        ≤ ‖iteratedFDeriv ℝ (n + 1) ((coordinateDerivative k)^[j] f) x‖ :=
          coordH8Frechet_norm_iteratedFDeriv_coordinateDerivative_le k _ hg n x
      _ ≤ ‖iteratedFDeriv ℝ (n + 1 + j) f x‖ := hbound (n + 1) x
      _ = ‖iteratedFDeriv ℝ (n + (j + 1)) f x‖ := by
          rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- The literal ordered canonical partial is bounded by the Frechet jet of its order. -/
theorem coordH8Frechet_norm_canonicalCoordinatePartial_le (alpha : Fin 3 → Fin 9)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    ‖canonicalCoordinatePartial alpha f x‖ ≤
      ‖iteratedFDeriv ℝ (multiIndexOrder alpha) f x‖ := by
  obtain ⟨h2, b2⟩ := coordH8Frechet_iterate 2 (alpha 2).val f hf
  obtain ⟨h1, b1⟩ := coordH8Frechet_iterate 1 (alpha 1).val _ h2
  obtain ⟨_, b0⟩ := coordH8Frechet_iterate 0 (alpha 0).val _ h1
  have horder : multiIndexOrder alpha = (alpha 0).val + (alpha 1).val + (alpha 2).val := by
    first
      | simp only [multiIndexOrder, Fin.sum_univ_three]
      | simp [multiIndexOrder, Fin.sum_univ_three]
  have h0 := b0 0 x
  rw [norm_iteratedFDeriv_zero] at h0
  calc ‖canonicalCoordinatePartial alpha f x‖
      = ‖((coordinateDerivative 0)^[(alpha 0).val]
          (((coordinateDerivative 1)^[(alpha 1).val])
            (((coordinateDerivative 2)^[(alpha 2).val]) f))) x‖ := rfl
    _ ≤ _ := h0
    _ ≤ _ := b1 _ x
    _ ≤ _ := b2 _ x
    _ = ‖iteratedFDeriv ℝ (multiIndexOrder alpha) f x‖ := by
        rw [horder, Nat.zero_add]

/-- Matrix coordinate evaluation is a contraction for the inherited Elementwise norm. -/
theorem coordH8Frechet_matrixEntry (h : MatrixField) (hh : ContDiff ℝ ∞ h) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y => h y i j) ∧ ∀ (n : ℕ) (x : R3),
      ‖iteratedFDeriv ℝ n (fun y => h y i j) x‖ ≤ ‖iteratedFDeriv ℝ n h x‖ := by
  let Lin : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := fun A B => by first | rfl | simp
      map_smul' := fun c A => by first | rfl | simp }
  have hLin : ∀ A : Matrix (Fin 3) (Fin 3) ℝ, ‖Lin A‖ ≤ 1 * ‖A‖ := fun A => by
    rw [one_mul]
    first
      | exact Matrix.norm_entry_le_entrywise_sup_norm A
      | simpa [Lin] using Matrix.norm_entry_le_entrywise_sup_norm A (i := i) (j := j)
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ := Lin.mkContinuous 1 hLin
  have hcomp : (fun y => h y i j) = L ∘ h := by
    first
      | rfl
      | (funext y; rfl)
      | (funext y; simp [L, Lin])
  rw [hcomp]
  refine ⟨L.contDiff.comp hh, fun n x => ?_⟩
  exact norm_iteratedFDeriv_comp_left_le_of_contracting
    R3 (Matrix (Fin 3) (Fin 3) ℝ) ℝ L
    (fun A => by change ‖Lin A‖ ≤ ‖A‖; simpa only [one_mul] using hLin A)
    h x hh.contDiffAt n

/-- Explicit comparison of the Euclidean tensor norm of the nine literal partials with
the Elementwise/operator Frechet jet norm. -/
theorem coordH8Frechet_norm_coordinateTensorPartial_le (alpha : Fin 3 → Fin 9)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (x : R3) :
    ‖coordinateTensorPartial alpha h x‖ ≤
      3 * ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖ := by
  have hM0 : 0 ≤ ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖ := norm_nonneg _
  have hT0 : 0 ≤ ‖coordinateTensorPartial alpha h x‖ := norm_nonneg _
  have hentry : ∀ ij : Fin 3 × Fin 3, ‖coordinateTensorPartial alpha h x ij‖ ≤
      ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖ := by
    intro ij
    obtain ⟨hc, hb⟩ := coordH8Frechet_matrixEntry h hh ij.1 ij.2
    calc ‖coordinateTensorPartial alpha h x ij‖
        = ‖canonicalCoordinatePartial alpha (fun y => h y ij.1 ij.2) x‖ := by
          first
            | rfl
            | simp only [coordinateTensorPartial, WithLp.ofLp_toLp]
            | simp [coordinateTensorPartial]
      _ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder alpha) (fun y => h y ij.1 ij.2) x‖ :=
          coordH8Frechet_norm_canonicalCoordinatePartial_le alpha _ hc x
      _ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖ := hb _ x
  have hsq : ‖coordinateTensorPartial alpha h x‖ ^ 2 ≤
      (3 * ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖) ^ 2 :=
    calc ‖coordinateTensorPartial alpha h x‖ ^ 2
        = ∑ ij : Fin 3 × Fin 3, ‖coordinateTensorPartial alpha h x ij‖ ^ 2 :=
          PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ ij : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖ ^ 2 := by
          refine Finset.sum_le_sum (fun ij _ => ?_)
          first
            | (rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) (hentry ij))
            | nlinarith [norm_nonneg (coordinateTensorPartial alpha h x ij), hentry ij]
      _ = (3 * ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h x‖) ^ 2 := by
          first
            | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
                nsmul_eq_mul]; push_cast; ring)
            | (simp [Finset.sum_const]; ring)
            | norm_num [Finset.sum_const]
            | (norm_num [Finset.sum_const]; ring)
  first
    | nlinarith [hsq, hT0, hM0]
    | exact (mul_self_le_mul_self_iff hT0 (by positivity)).2 (by simpa only [sq] using hsq)

theorem exists_coordinateH8_le_frechet_jet_sum :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (h : MatrixField), ContDiff ℝ ∞ h → ∀ y : R3,
      coordinateH8 h y ≤ A * ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin 3 → Fin 9) : ℝ) := Nat.cast_nonneg _
  refine ⟨3 * (Fintype.card (Fin 3 → Fin 9) : ℝ) + 1, by linarith, ?_⟩
  intro h hh y
  have hS0 : 0 ≤ ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ :=
    Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have hterm : ∀ alpha : Fin 3 → Fin 9,
      (if multiIndexOrder alpha ≤ 8 then ‖coordinateTensorPartial alpha h y‖ else 0) ≤
        3 * ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by
    intro alpha
    split_ifs with ha
    · calc ‖coordinateTensorPartial alpha h y‖
          ≤ 3 * ‖iteratedFDeriv ℝ (multiIndexOrder alpha) h y‖ :=
            coordH8Frechet_norm_coordinateTensorPartial_le alpha h hh y
        _ ≤ 3 * ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Finset.single_le_sum (f := fun n => ‖iteratedFDeriv ℝ n h y‖)
              (fun n _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    · linarith
  calc coordinateH8 h y
      ≤ ∑ _alpha : Fin 3 → Fin 9, 3 * ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by
        unfold coordinateH8
        exact Finset.sum_le_sum (fun alpha _ => hterm alpha)
    _ = 3 * (Fintype.card (Fin 3 → Fin 9) : ℝ) *
          ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by
        first
          | (rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring)
          | (simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring)
    _ ≤ 3 * (Fintype.card (Fin 3 → Fin 9) : ℝ) *
          ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ +
          ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := le_add_of_nonneg_right hS0
    _ = (3 * (Fintype.card (Fin 3 → Fin 9) : ℝ) + 1) *
          ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n h y‖ := by ring

theorem exists_coordinateH8_le_source_jet_sum_of_binomial_recovery :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (E : MatrixField), ContDiff ℝ ∞ E →
      ∀ (F : Fin 5 → R3 → ℝ) (C : ℝ), 0 ≤ C → ∀ y : R3,
      (∀ n : ℕ, n ≤ 8 →
        ‖iteratedFDeriv ℝ n E y‖ ≤ C * ∑ i ∈ Finset.range (n+1),
          (Nat.choose n i : ℝ) * ∑ k : Fin 5,
            ‖iteratedFDeriv ℝ (n-i+2) (F k) y‖) →
      coordinateH8 E y ≤ B * C *
        ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖ := by
  obtain ⟨A, hA1, hA⟩ := exists_coordinateH8_le_frechet_jet_sum
  have hW0 : 0 ≤ ∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) :=
    Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  refine ⟨A * ((∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1),
    (Nat.choose n i : ℝ)) + 1), ?_, ?_⟩
  · first
      | exact one_le_mul_of_one_le_of_one_le hA1 (by linarith)
      | nlinarith
  intro E hE F C hC y hrec
  have hT0 : 0 ≤ ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖ :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun m _ => norm_nonneg _))
  have hn : ∀ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n E y‖ ≤
      C * ((∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) *
        ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) := by
    intro n hn9
    have hn8 : n ≤ 8 := by
      have := Finset.mem_range.mp hn9
      omega
    refine (hrec n hn8).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hi' := Finset.mem_range.mp hi
    exact Finset.single_le_sum (f := fun m => ‖iteratedFDeriv ℝ m (F k) y‖)
      (fun m _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hsum : ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n E y‖ ≤
      C * ((∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) *
        ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) := by
    calc ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n E y‖
        ≤ ∑ n ∈ Finset.range 9, C * ((∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) *
            ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) :=
          Finset.sum_le_sum hn
      _ = C * ((∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) *
            ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hACT : 0 ≤ A * C *
      ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖ :=
    mul_nonneg (mul_nonneg (by linarith) hC) hT0
  calc coordinateH8 E y ≤ A * ∑ n ∈ Finset.range 9, ‖iteratedFDeriv ℝ n E y‖ := hA E hE y
    _ ≤ A * (C * ((∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) *
          ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖)) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ = A * C * (∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) *
          (∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) := by
        ring
    _ ≤ A * C * (∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖) *
          (∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) +
          A * C * ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖ :=
        le_add_of_nonneg_right hACT
    _ = A * ((∑ n ∈ Finset.range 9, ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ)) + 1) *
          C * ∑ k : Fin 5, ∑ m ∈ Finset.range 11, ‖iteratedFDeriv ℝ m (F k) y‖ := by
        ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
