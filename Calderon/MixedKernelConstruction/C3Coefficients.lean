import Calderon.MixedKernelConstruction.C3Spectral

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable

section CoefficientOperator
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (μ : ι → ℝ)

/-- The actual real-valued coefficient functional from cross:coefficient-extension. -/
def singularCoefficient (i : ι) : F →L[ℝ] ℝ :=
  (μ i ^ 2)⁻¹ • innerSL ℝ (R (w i))

@[simp] theorem singularCoefficient_apply (i : ι) (G : F) :
    singularCoefficient R w μ i G = (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G := by
  rfl

theorem singularCoefficient_norm_le (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (i : ι) : ‖singularCoefficient R w μ i‖ ≤ (μ i)⁻¹ := by
  have hnorm : ‖R (w i)‖ = μ i := by
    apply (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp
    calc
      ‖R (w i)‖ ^ 2 = inner ℝ (R (w i)) (R (w i)) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = μ i ^ 2 := by rw [hgram, if_pos rfl]
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (hμ i).le)
  intro G
  change |(μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G| ≤ _
  calc
    _ = (μ i ^ 2)⁻¹ * |inner ℝ (R (w i)) G| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    _ ≤ (μ i ^ 2)⁻¹ * (‖R (w i)‖ * ‖G‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_nonneg.mpr (sq_nonneg _))
    _ = (μ i)⁻¹ * ‖G‖ := by
      rw [hnorm]
      field_simp

/-- Actual measurable L2 coefficient family, constructed using the pointwise Lp action. -/
def singularCoefficientLp {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (i : ι) : Lp ℝ 2 ν :=
  (singularCoefficient R w μ i).compLp Q

theorem singularCoefficientLp_ae {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (i : ι) :
    (singularCoefficientLp R w μ ν Q i : Y → ℝ) =ᵐ[ν]
      fun y => (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) (Q y) :=
  (singularCoefficient R w μ i).coeFn_compLp Q

theorem singularCoefficientLp_norm_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (i : ι) : ‖singularCoefficientLp R w μ ν Q i‖ ≤ (μ i)⁻¹ * ‖Q‖ := by
  exact ((singularCoefficient R w μ i).norm_compLp_le Q).trans
    (mul_le_mul_of_nonneg_right (singularCoefficient_norm_le R w μ hμ hgram i)
      (norm_nonneg Q))

variable [CompleteSpace E] [CompleteSpace F]

/-- Agreement on the actual restriction range, by the SAME eigen equation. -/
theorem singularCoefficient_restrict (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i)
    (u : E) (i : ι) : singularCoefficient R w μ i (R u) = inner ℝ (w i) u := by
  rw [singularCoefficient_apply, ← R.adjoint_inner_left u (R (w i))]
  change (μ i ^ 2)⁻¹ * inner ℝ ((ContinuousLinearMap.adjoint R ∘L R) (w i)) u = _
  rw [heigen, real_inner_smul_left, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 (hμ i).ne'), one_mul]

/-- Reconstruction is only claimed on the actual range of R. -/
theorem hasSum_singularCoefficient_restrict (b : HilbertBasis ι ℝ E)
    (hwb : ∀ i, w i = b i) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i)
    (u : E) : HasSum (fun i => singularCoefficient R w μ i (R u) • R (w i)) (R u) := by
  have hs := R.hasSum (b.hasSum_repr u)
  simpa only [map_smul, b.repr_apply_apply, singularCoefficient_restrict R w μ hμ heigen,
    hwb] using hs

end CoefficientOperator

section NativeSlice
open EnergyBridge

/-- An actual smooth L2 solution lies in the SAME native closed harmonic carrier. -/
def harmonicSlice (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) :
    harmonicSub D hD A hA := by
  refine ⟨hf.toLp f, ?_⟩
  change hf.toLp f ∈ closure {v : Lp ℝ 2 ((volume : Measure R3).restrict D) |
    ∃ U : R3 → ℝ, ContDiffOn ℝ ∞ U D ∧
      (∀ x ∈ D, divCoeffGrad A U x = 0) ∧
      (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict D] U}
  exact subset_closure ⟨f, hfs, hfP, hf.coeFn_toLp⟩

theorem harmonicRestrict_harmonicSlice_ae (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (S : Set R3) (hSD : S ⊆ D)
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) :
    (harmonicRestrict D hD A hA S hSD (harmonicSlice D hD A hA f hf hfs hfP) :
      R3 → ℝ) =ᵐ[(volume : Measure R3).restrict S] f := by
  have hr := Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (show (volume : Measure R3).restrict S ≤
      (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
      by simpa only [one_smul] using Measure.restrict_mono_set volume hSD) (hf.toLp f)
  exact hr.trans (ae_restrict_of_ae_restrict_of_subset hSD hf.coeFn_toLp)

/-- Exact manuscript integral formula for an actual native smooth harmonic slice. -/
theorem singularCoefficient_harmonicSlice_integral (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (S : Set R3) (hSD : S ⊆ D) {ι : Type*}
    (w : ι → harmonicSub D hD A hA) (μ : ι → ℝ)
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) (i : ι) :
    singularCoefficient (harmonicRestrict D hD A hA S hSD) w μ i
        (harmonicRestrict D hD A hA S hSD (harmonicSlice D hD A hA f hf hfs hfP)) =
      (μ i ^ 2)⁻¹ * ∫ x in S, f x *
        (harmonicRestrict D hD A hA S hSD (w i)) x := by
  rw [singularCoefficient_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [harmonicRestrict_harmonicSlice_ae D hD A hA S hSD f hf hfs hfP] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

/-- The extended integral agrees with the original Hilbert coefficient. -/
theorem harmonicSlice_coefficient_agreement (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (S : Set R3) (hSD : S ⊆ D) {ι : Type*}
    (w : HilbertBasis ι ℝ (harmonicSub D hD A hA)) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i,
      (ContinuousLinearMap.adjoint (harmonicRestrict D hD A hA S hSD) ∘L
        harmonicRestrict D hD A hA S hSD) (w i) = μ i ^ 2 • w i)
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) (i : ι) :
    (μ i ^ 2)⁻¹ * (∫ x in S, f x * (harmonicRestrict D hD A hA S hSD (w i)) x) =
      w.repr (harmonicSlice D hD A hA f hf hfs hfP) i := by
  rw [← singularCoefficient_harmonicSlice_integral D hD A hA S hSD w μ f hf hfs hfP i,
    singularCoefficient_restrict _ _ _ hμ heigen, w.repr_apply_apply]

/-- L2 reconstruction of the SAME native restricted slice by the integral coefficients. -/
theorem harmonicSlice_hasSum_integral_coefficients (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (S : Set R3) (hSD : S ⊆ D) {ι : Type*}
    (w : HilbertBasis ι ℝ (harmonicSub D hD A hA)) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i,
      (ContinuousLinearMap.adjoint (harmonicRestrict D hD A hA S hSD) ∘L
        harmonicRestrict D hD A hA S hSD) (w i) = μ i ^ 2 • w i)
    (f : R3 → ℝ) (hf : MemLp f 2 ((volume : Measure R3).restrict D))
    (hfs : ContDiffOn ℝ ∞ f D) (hfP : ∀ x ∈ D, divCoeffGrad A f x = 0) :
    HasSum (fun i => ((μ i ^ 2)⁻¹ *
        ∫ x in S, f x * (harmonicRestrict D hD A hA S hSD (w i)) x) •
      harmonicRestrict D hD A hA S hSD (w i))
      (harmonicRestrict D hD A hA S hSD (harmonicSlice D hD A hA f hf hfs hfP)) := by
  have hs := hasSum_singularCoefficient_restrict
    (harmonicRestrict D hD A hA S hSD) w μ w (fun _ => rfl) hμ heigen
    (harmonicSlice D hD A hA f hf hfs hfP)
  simpa only [singularCoefficient_harmonicSlice_integral] using hs

end NativeSlice
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
